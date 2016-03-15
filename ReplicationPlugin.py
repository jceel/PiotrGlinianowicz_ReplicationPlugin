#
# Copyright 2015 iXsystems, Inc.
# All rights reserved
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted providing that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
# IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
# OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
# HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
# STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
# IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
#
#####################################################################

import enum
import io
import errno
import re
import logging
import paramiko
from paramiko import RSAKey, AuthenticationException
from datetime import datetime
from dateutil.parser import parse as parse_datetime
from task import Provider, Task, ProgressTask, VerifyException, TaskException, TaskWarning, query
from freenas.dispatcher.rpc import RpcException, SchemaHelper as h, description, accepts, returns, private
from freenas.dispatcher.client import Client
from freenas.utils import to_timedelta, first_or_default
from freenas.utils.query import wrap
from lib import sendzfs
import libzfs
import socket
import threading
import os
import uuid
from itsdangerous import TimestampSigner

"""
# Bandwidth Limit.
if  bandlim != 0:
    throttle = '/usr/local/bin/throttle -K %d | ' % bandlim
else:
    throttle = ''

#
# Build the SSH command
#

# Cipher
if cipher == 'fast':
    sshcmd = ('/usr/bin/ssh -c arcfour256,arcfour128,blowfish-cbc,'
              'aes128-ctr,aes192-ctr,aes256-ctr -i /data/ssh/replication'
              ' -o BatchMode=yes -o StrictHostKeyChecking=yes'
              # There's nothing magical about ConnectTimeout, it's an average
              # of wiliam and josh's thoughts on a Wednesday morning.
              # It will prevent hunging in the status of "Sending".
              ' -o ConnectTimeout=7'
             )
elif cipher == 'disabled':
    sshcmd = ('/usr/bin/ssh -ononeenabled=yes -ononeswitch=yes -i /data/ssh/replication -o BatchMode=yes'
              ' -o StrictHostKeyChecking=yes'
              ' -o ConnectTimeout=7')
else:
    sshcmd = ('/usr/bin/ssh -i /data/ssh/replication -o BatchMode=yes'
              ' -o StrictHostKeyChecking=yes'
              ' -o ConnectTimeout=7')

# Remote IP/hostname and port.  This concludes the preparation task to build SSH command
sshcmd = '%s -p %d %s' % (sshcmd, remote_port, remote)
"""

logger = logging.getLogger(__name__)
SYSTEM_RE = re.compile('^[^/]+/.system.*')
AUTOSNAP_RE = re.compile(
    '^(?P<prefix>\w+)-(?P<year>\d{4})(?P<month>\d{2})(?P<day>\d{2})'
    '.(?P<hour>\d{2})(?P<minute>\d{2})-(?P<lifetime>\d+[hdwmy])(-(?P<sequence>\d+))?$'
)
SSH_OPTIONS = {
    'NONE': [
        '-ononeenabled=yes',
        '-ononeswitch=yes',
        '-o BatchMode=yes',
        '-o ConnectTimeout=7'
    ],
    'FAST': [
        '-c arcfour256,arcfour128,blowfish-cbc,aes128-ctr,aes192-ctr,aes256-ctr',
        '-o BatchMode=yes',
        '-o ConnectTimeout=7'
    ],
    'NORMAL': [
        '-o BatchMode=yes',
        '-o ConnectTimeout=7'
    ]
}


class ReplicationActionType(enum.Enum):
    SEND_STREAM = 1
    DELETE_SNAPSHOTS = 2
    DELETE_DATASET = 3


class ReplicationAction(object):
    def __init__(self, type, localfs, remotefs, **kwargs):
        self.type = type
        self.localfs = localfs
        self.remotefs = remotefs
        for k, v in kwargs.items():
            setattr(self, k, v)

    def __getstate__(self):
        d = dict(self.__dict__)
        d['type'] = d['type'].name
        return d

class ReplicationTcpTransportCtrl(object):
    """ Top level class for the Replication TCP Transport Layer
    The Replication TCP Transport Controller class contains Replication TCP Server and TCP Client modules. 
    The class instantiates : - TCP Server for Replication PUSH mode 
                             - TCP Client for Replication PULL mode 
    Public methods available for each mode are distinguished by the 'push__'/'pull__' prefixes 
    This class should be instantiated inside the class inheriting after Task class
    to assure correct functioning of the _get_host() method of TCP Server

    Configuration parameters available are : 
        - host                : Server IP     - override the _get_host() method 
        - port                : Server Port   - override the _get_port() method
        - buff_size           : Transmission buffer size (default = 1024)
        - remote_conn_timeout : Timeout value for initial request from remote site
        - token_valid_timeout : Timeout value embedded in each transaction token (default = None) 

    Usage on PUSH side:
        1. tcp_ctrl = ReplicationTcpTransportCtrl(self,mode='PUSH')
        1. tcp_ctrl.push__prepare_transaction_infos(actions) : Prepare local and remote list of transactions to occur 
                                                               (snapshots to send) 
        2. tcp_ctrl.push__start_tcp_server_thread(local_trans_infos) : Start the TCP server and provide 
                                                                       all required transaction information
        3. tcp_ctrl.push__initiate_replication_rpc(remote_trans_info) : For each snapshot to send execute separate 
                                                                        RPC call with required transacion information
    Usage on PULL side:
        1. tcp_ctrl = ReplicationTcpTransportCtrl(self,mode='PULL')
        2. tcp_ctrl.pull__replicate()
    """ 
    def __init__(self, parent, mode='PUSH'):
        self.parent              = parent
        self.mode                = mode
        self.host                = self._get_host()
        self.port                = self._get_port()
        self.buff_size           = 1024
        self.remote_conn_timeout = 20
        self.token_valid_timeout = None
        # Both validation messages must be same length!
        self.validation_resp_ok  = 'validation_ok'
        self.validation_resp_err = 'validation_er'
        self.validation_resp_len = len(self.validation_resp_ok)
        logger                   = logging.getLogger(__name__)
        self.tcp_server          = _ReplicationTcpServer(parent=self) if mode == 'PUSH' else None
        self.tcp_client          = _ReplicationTcpClient(parent=self) if mode == 'PULL' else None

    # PUSH Mode Methods
    def push__prepare_transaction_infos(self, actions):
        """
        Method accepts list of actions as prepared in the run method of ReplicateDatasetTask
        It returns two lists of transaction information : local_trans_infos, remote_trans_infos
        Transaction information contains : 
            - tcp connection details
            - authentication and encoding keys 
            - zfs resources
        'local_trans_infos' is passed to the TCP Server for handling incoming transfer requests
        'remote_trans_infos' list is passed to remote partner via RPC or other method secure method
        """
        logger.debug('Tcp Transport Controller : Prepare TCP Transactions information')

        local_trans_infos   = []
        remote_trans_infos  = []

        for action in actions:
            if action.type == ReplicationActionType.SEND_STREAM:
                secret_key, token = self._get_key_token_pair(action.snapshot)
                logger.debug('Tcp Transport Controller : Generated secret key and token : %s %s', secret_key, token)
                local_trans_info = {
                    'secret_key'    : secret_key,
                    'token_size'    : len(token),
                    'aes_key'       : self._get_aes_key(),
                    'tcp_port'      : self.port,
                    'tcp_host'      : self.host,
                    'dataset'       : action.localfs,
                    'tosnap'        : action.snapshot,
                    'fromsnap'      : action.anchor,
                    'remotefs'      : action.remotefs,
                }
                remote_trans_info = {
                    'token'         : token,
                    'aes_key'       : self._get_aes_key(),
                    'tcp_port'      : self.port,
                    'tcp_host'      : self.host,
                    'dataset'       : action.localfs,
                    'tosnap'        : action.snapshot,
                    'fromsnap'      : action.anchor,
                    'remotefs'      : action.remotefs,
                }
                local_trans_infos.append(local_trans_info)
                remote_trans_infos.append(remote_trans_info)

        logger.debug('Tcp Transport Controller : Number of snaphots to send: %d ', len(local_trans_infos))
        logger.debug('Tcp Transport Controller : local_trans_infos = %s', str(local_trans_infos))
        logger.debug('Tcp Transport Controller : remote_trans_infos = %s', str(remote_trans_infos))
        return local_trans_infos, remote_trans_infos

    def push__start_tcp_server_thread(self,local_trans_infos):
        """Start the TCP Server and pass information about all expected transactions to the service loop thread"""
        self.tcp_server.start_server()

        tcps_t = threading.Thread(target=self.tcp_server.service_loop,name='ReplicationTCPServer',kwargs={'trans_infos':local_trans_infos})
        tcps_t.setDaemon(True)
        tcps_t.start()

    def push__initiate_replication_rpc(self, remote, trans_info):
        """
        Initiate the RPC to Replication PULL side and pass required transaction information
        For every snapshot to send there should be a separate RPC initiated
        """
        logger.debug('Tcp Transport Controller : Initiating RPC')
        remote_client = get_client(remote)
        remote_client.call_task_sync(
            'replication.replicate_dataset_pull',
            trans_info
        )
        remote_client.disconnect()
        logger.debug('Tcp Transport Controller : RPC Finished')

    # PULL Mode Methods
    def pull__replicate(self, trans_info):
        return self.tcp_client.pull__replicate(trans_info)

    # Utility Methods
    def _get_host(self):
        """Get the first ipv4 address from the list of system ips"""
        ips = self.parent.dispatcher.call_sync('network.config.get_my_ips')
        for ip in ips:
            try:
                socket.inet_aton(ip)
                return ip
            except:
                continue
        raise ValueError('No IPv4 address found for Replication TCP Server')

    def _get_port(self):
        return 53213

    def _get_key_token_pair(self, snapname):
        """
        Generate (secret_key,token) pair for TCP snapshot transfer validation
        Function utilizes the 'itsdangerous' module
        """
        secret_key = self._get_secret_key()
        s = TimestampSigner(secret_key)
        return secret_key, str(s.sign(snapname),'ascii')

    def _unsign_tcp_token(self, secret_key, token):
        """
        Return unsigned string from token
        Token timeout value can be checked depending on the ReplicationTCPTransportCtrl settings (self.token_valid_timeout)
        """
        s = TimestampSigner(secret_key)
        return str(s.unsign(token,max_age=self.token_valid_timeout),'ascii')

    def _get_secret_key(self):
        """Provide secret-key for 'itsdangerous' cipher algorithm"""
        return str(uuid.uuid4())

    def _get_aes_key(self):
        """AES functionality not implemented yet"""
        return '1'

class _ReplicationTcpServer(object):
    """Subcomponent class of the ReplicationTcpTransportCtrl
    This class is used on the PUSH side of the Replication link
    It requires transaction information list : local_trans_infos[] as prepared 
    by the method ReplicationTcpTransportCtrl.push__prepare_transaction_infos()

    The class extracts input transaction information, starts the TCP server
    and waits for incoming connections from the PULL side of the link.
    After validating the received transaction token from incoming request 
    a thread is dispatched to handle the rest of the transfer.
    Each request handles transfer of a single snapshot from the transaction list
    """
    def __init__(self, parent):
        self.parent              = parent
        self.host                = parent.host
        self.port                = parent.port
        self.buff_size           = parent.buff_size
        self.exp_trans_infos     = []
        self.threads             = []
        self.sock                = ''
        self.curr_conn           = ''
        self.validation_resp_ok  = parent.validation_resp_ok
        self.validation_resp_err = parent.validation_resp_err
        self.validation_resp_len = parent.validation_resp_len
        logger                   = logging.getLogger(__name__)

    def start_server(self):
        logger.debug('Tcp Server : Start Server')

        self.sock = socket.socket(socket.AF_INET,socket.SOCK_STREAM)
        # Could add retry loop or change the port
        try: 
            self.sock.bind((self.host,self.port))
        except Exception as e:
            logger.debug('Tcp Server : ERROR Could not connect')
            self.sock.close()
            raise e
        
    def service_loop(self,trans_infos):
        """
        Server will automatically shutdown after all expected connections are finished
        or after 'bind' or 'validate' errors 
        ! Currently server only works for sequential transfer requests from remote partner
        """
        logger.debug('Tcp Server : Service Loop')
        logger.debug('Tcp Server : trans_infos  = %s' , str(trans_infos))

        self.exp_trans_infos = trans_infos

        self.sock.listen(len(self.exp_trans_infos))
        logger.debug('TCP Server : Listening at : %s ', str(self.host)+':'+str(self.port))

        self.sock.settimeout(self.parent.remote_conn_timeout)
        while len(self.exp_trans_infos):
            try:
                self.curr_conn, addr = self.sock.accept()
            except socket.timeout as tout:
                logger.debug('TCP Server : Timeout waiting for initial request')
                self._stop_server()
                raise tout
            else:
                self.sock.settimeout(None)
                logger.debug('TCP Server : New connection at : %s ', str(addr))
                self._validate_request()
                self._dispatch_request()

        logger.debug('TCP Server : TCP Service Loop Exiting')
        for t in self.threads:
            t.join()

        self._stop_server()

    def _validate_request(self):
        """Receive and validate the token from the Replication PULL side"""
        logger.debug('TCP Server : Validate Request')
        logger.debug('TCP Server : Validate Request - getting validation key from client')

        exp_token_size  = self.exp_trans_infos[0]['token_size']
        secret_key      = self.exp_trans_infos[0]['secret_key']
        tosnap          = self.exp_trans_infos[0]['tosnap']
        recv_token      = ''
        while (len(recv_token) < exp_token_size):
            recv_token += str(self.curr_conn.recv(exp_token_size-len(recv_token)),'ascii')
        
        logger.debug('TCP Server : Validate Request - key from client : %s', recv_token)

        try:
            recv_token = self._unsign_tcp_token(secret_key,recv_token)
        except Exception as e:
            logger.debug('TCP Server : Validate Request - TOKEN ERROR')
            self._stop_curr_conn()
            self._stop_server()
            raise e
        else:
            logger.debug('TCP Server : Validate Request - token unsigned correctly : %s', recv_token)

            if (tosnap != recv_token):
                logger.debug('TCP Server : Validate Request - VALIDATION ERROR')
                self.curr_conn.sendall(bytes(self.validation_resp_err,'ascii'))
                self._stop_curr_conn()
                self._stop_server()
                raise ValueError('TCP Server : Snapshot name received in token does not match')
            else:
                logger.debug('TCP Server : Validate Request - VALIDATION OK')
                self.curr_conn.sendall(bytes(self.validation_resp_ok,'ascii'))

    def _dispatch_request(self):
        """Start a thread to service new transfer request"""
        logger.debug('TCP Server : Dispatch Request')

        trans_info = self.exp_trans_infos.pop(0)
        tcpc_t = threading.Thread(target=self._handle_request,name='ReplicationTCPRequestHandler'+str(len(self.threads)),kwargs={'conn':self.curr_conn, 'trans_info':trans_info})
        tcpc_t.setDaemon(True)
        self.threads.append(tcpc_t)
        tcpc_t.start()

    def _handle_request(self, conn, trans_info):
        """Transfer the actual snapshot data to the PULL side"""
        logger.debug('TCP Server : Request Handler')

        dataset      = trans_info['dataset' ]
        tosnap       = trans_info['tosnap'  ]
        fromsnap     = trans_info['fromsnap']

        # Get snapshot and serialize
        zfs = libzfs.ZFS()
        snap = zfs.get_snapshot("{0}@{1}".format(dataset,tosnap))
        snap_readfd,snap_writefd = os.pipe()
        snap.send(snap_writefd,fromname=fromsnap,flags={
            libzfs.SendFlag.PROGRESS,
            libzfs.SendFlag.PROPS
        })
        os.close(snap_writefd)
        # Start Tcp transfer
        i=0
        data = os.read(snap_readfd,self.buff_size)
        while (data):
            i += 1
            conn.sendall(data)
            data = os.read(snap_readfd,self.buff_size)

        logger.debug('TCP Server : Request Handler - total packets sent : %d',i)
        os.close(snap_readfd)
        conn.shutdown(socket.SHUT_RDWR)
        conn.close()
        logger.debug('TCP Server : Request Handler - exiting')

    def _stop_server(self):
        logger.debug('TCP Server : Server shutting down')
        self.sock.shutdown(socket.SHUT_RDWR)
        self.sock.close()

    def _stop_current_conn(self):
        logger.debug('TCP Server : Closing current connection')
        self.curr_conn.shutdown(socket.SHUT_RDWR)
        self.curr_conn.close()

    def _unsign_tcp_token(self, secret_key, recv_token):
        """Parent class unsign algorithm is used"""
        return self.parent._unsign_tcp_token(secret_key, recv_token)

class _ReplicationTcpClient(object):
    """Subcomponent class of the ReplicationTcpTransportCtrl
    This class is used on the PULL side of the Replication link.
    It requires transaction information list : remote_trans_infos[] as prepared 
    by the method ReplicationTcpTransportCtrl.push__prepare_transaction_infos()

    The class extracts the input transaction information 
    and connects to TCP Server on the PUSH side of the link.
    After validating connection with the token the data is transffered.
    Replication is executed with calls to the py-libzfs library
    """
    def __init__(self, parent):
        self.parent              = parent
        self.host                = ''
        self.port                = ''
        self.buff_size           = parent.buff_size
        self.trans_info          = {}
        self.sock                = ''
        self.validation_resp_ok  = parent.validation_resp_ok
        self.validation_resp_err = parent.validation_resp_err
        self.validation_resp_len = parent.validation_resp_len
        logger                   = logging.getLogger(__name__)

    def pull__replicate(self, trans_info):
        """Execute all the steps of replication process"""
        logger.debug('Tcp Client : PULL Replicate Start')
        self.connect(trans_info)
        self.validate()
        self.receive_and_replicate()
        self.disconnect()
        logger.debug('Tcp Client : PULL Replicate End')

    def connect(self, trans_info):
        """Extract the PUSH TCP server details from transaction information and connect"""
        logger.debug('Tcp Client : Connect')
        self.trans_info = trans_info
        self.port       = trans_info['tcp_port']
        self.host       = trans_info['tcp_host']

        self.sock = socket.socket(socket.AF_INET,socket.SOCK_STREAM)

        try:
            self.sock.connect((self.host,self.port))
        except socket.error as err:
            logger.debug('Tcp Client : Connection error')
            self.sock.disconnect()
            raise err
        else:
            logger.debug('Tcp Client : Connected Successfully')

    def disconnect(self):
        logger.debug('Tcp Client : Closing Connection')
        self.sock.shutdown(socket.SHUT_RDWR)
        self.sock.close()

    def validate(self):
        """Validate the connection by sending the transaction token to the server"""
        logger.debug('TCP Client : Send validation key')
        token = self.trans_info['token']

        self.sock.sendall(bytes(token,'ascii'))

        logger.debug('TCP Client : Waiting for validation resp')
        auth_resp = str(self.sock.recv(self.validation_resp_len),'ascii')
        logger.debug('TCP Client : Received validation auth_resp : %s' % auth_resp)

        if (auth_resp != self.validation_resp_ok):
            self.sock.disconnect()
            logger.debug('TCP Client Validation Error Received from server, exiting')
            raise ValueError("Received validation error response from server")

    def receive_and_replicate(self):
        """Receive data through TCP socket and replicate 
        Method uses py-libzfs calls for replication
        """
        logger.debug('TCP Client : Receive and replicate')
        localfs = self.trans_info['remotefs']

        snap_readfd, snap_writefd = os.pipe()
        i = 0
        data = self.sock.recv(self.buff_size)
        while (data):
            i += 1
            os.write(snap_writefd,data)
            data = self.sock.recv(self.buff_size)
        logger.debug('TCP Client : Total packets received : %d', i)
        logger.debug('TCP Client : Done receiving data')
        os.close(snap_writefd)
        
        zfs = libzfs.ZFS()
        dataset = zfs.get_dataset(localfs)
        dataset.receive(snap_readfd,force=True)
        
        os.close(snap_readfd)


class ReplicationProvider(Provider):
    def get_public_key(self):
        return self.configstore.get('replication.key.public')

    def scan_keys_on_host(self, hostname):
        return self.dispatcher.call_task_sync('replication.scan_hostkey', hostname)


class ReplicationLinkProvider(Provider):
    @query('replication-link')
    def query(self, filter=None, params=None):
        return self.datastore.query(
            'replication.links', *(filter or []), **(params or {})
        )

    def get_one(self, name):
        if self.datastore.exists('replication.links', ('name', '=', name)):
            return self.datastore.get_one('replication.links', ('name', '=', name))
        else:
            return None


@accepts(str)
class ScanHostKeyTask(Task):
    def verify(self, hostname):
        return []

    def run(self, hostname):
        transport = paramiko.transport.Transport(hostname)
        transport.start_client()
        key = transport.get_remote_server_key()
        return {
            'name': key.get_name(),
            'key': key.get_base64()
        }


@description("Sets up bi-directional replication link")
@accepts(h.all_of(
        h.ref('replication-link'),
        h.required('name', 'partners', 'master', 'datasets', 'replicate_services', 'bidirectional')
    ),
    h.one_of(str, None)
)
class ReplicationCreate(Task):
    def verify(self, link, password=None):
        ip_matches = False
        ips = self.dispatcher.call_sync('network.config.get_my_ips')
        for ip in ips:
            for partner in link['partners']:
                if '@' not in partner:
                    raise VerifyException(
                        errno.EINVAL,
                        'Please provide bi-directional replication link partners as username@host'
                    )
                if partner.endswith(ip):
                    ip_matches = True

        if not ip_matches:
            raise VerifyException(errno.EINVAL, 'Provided partner IPs do not create a valid pair. Check addresses.')

        if self.datastore.exists('replication.links', ('name', '=', link['name'])):
            raise VerifyException(errno.EEXIST, 'Bi-directional replication link with same name already exists')

        return []

    def run(self, link, password=None):
        link['id'] = link['name']
        link['update_date'] = str(datetime.utcnow())

        is_master, remote = get_bidir_link_state(self.dispatcher, link)

        if is_master:
            with self.dispatcher.get_lock('volumes'):
                remote_client = get_client(remote)

                for volume in link['datasets']:
                    if not self.datastore.exists('volumes', ('id', '=', volume)):
                        raise TaskException(errno.ENOENT, 'Volume {0} not found'.format(volume))

                    for share in self.dispatcher.call_sync('share.get_related', volume):
                        remote_share = remote_client.call_sync(
                            'share.query',
                            [('name', '=', share['name'])],
                            {'single': True}
                        )
                        if remote_share:
                            raise TaskException(
                                errno.EEXIST,
                                'Share {0} already exists on {1}'.format(share['name'], remote.split('@', 1)[1])
                            )

                    for container in self.dispatcher.call_sync('container.query', [('target', '=', volume)]):
                        remote_container = remote_client.call_sync(
                            'container.query',
                            [('name', '=', container['name'])],
                            {'single': True}
                        )
                        if remote_container:
                            raise TaskException(
                                errno.EEXIST,
                                'Container {0} already exists on {1}'.format(container['name'], remote.split('@', 1)[1])
                            )

                for volume in link['datasets']:
                    remote_vol = remote_client.call_sync(
                        'volume.query',
                        [('id', '=', volume)],
                        {'single': True}
                    )
                    if not remote_vol:
                        try:
                            vol = self.datastore.get_one('volumes', ('id', '=', volume))
                            remote_client.call_task_sync(
                                'volume.create',
                                {
                                    'id': vol['id'],
                                    'type': vol['type'],
                                    'params': {'encryption': True if vol.get('encrypted') else False},
                                    'topology': vol['topology']
                                },
                                password
                            )
                        except RpcException as e:
                            raise TaskException(
                                e.code,
                                'Cannot create exact duplicate of {0} on {1}. Message: {2}'.format(
                                    volume,
                                    remote,
                                    e.message
                                )
                            )

                    vol_datasets = self.dispatcher.call_sync(
                        'zfs.dataset.query',
                        [('pool', '=', volume)],
                        {'sort': ['name']}
                    )
                    for dataset in vol_datasets:
                        remote_dataset = remote_client.call_sync(
                            'zfs.dataset.query',
                            [('name', '=', dataset['name'])],
                            {'single': True}
                        )
                        if not remote_dataset:
                            try:
                                if dataset['type'] == 'VOLUME':
                                    continue

                                dataset_properties = {
                                    'id': dataset['name'],
                                    'volume': dataset['pool']
                                }
                                if dataset['mountpoint']:
                                    dataset_properties['mountpoint'] = dataset['mountpoint']
                                remote_client.call_task_sync(
                                    'volume.dataset.create',
                                    dataset_properties
                                )
                            except RpcException as e:
                                raise TaskException(
                                    e.code,
                                    'Cannot create exact duplicate of {0} on {1}. Message: {2}'.format(
                                        dataset['name'],
                                        remote,
                                        e.message
                                    )
                                )

                remote_client.call_task_sync('replication.create', link)

                id = self.datastore.insert('replication.links', link)

                for volume in link['datasets']:
                    self.join_subtasks(self.run_subtask(
                        'replication.replicate_dataset',
                        volume,
                        volume,
                        {
                            'remote': remote,
                            'remote_dataset': volume,
                            'recursive': True
                        }
                    ))

                    if link['replicate_services']:
                        remote_client.call_task_sync('volume.autoimport', volume, 'containers')
                        remote_client.call_task_sync('volume.autoimport', volume, 'shares')

                set_bidir_link_state(remote_client, False, link['datasets'], True)
                remote_client.disconnect()

        else:
            id = self.datastore.insert('replication.links', link)

        self.dispatcher.dispatch_event('replication.changed', {
            'operation': 'create',
            'ids': [id]
        })


@description("Deletes bi-directional replication link")
@accepts(str, bool)
class ReplicationDelete(Task):
    def verify(self, name, scrub=False):
        if not self.datastore.exists('replication.links', ('name', '=', name)):
            raise VerifyException(errno.ENOENT, 'Bi-directional replication link {0} do not exist.'.format(name))

        return []

    def run(self, name, scrub=False):
        link = get_latest_bidir_link(self.dispatcher, self.datastore, name)
        is_master, remote = get_bidir_link_state(self.dispatcher, link)

        if not is_master and scrub:
            set_bidir_link_state(self.dispatcher, True, link['datasets'], False)
            with self.dispatcher.get_lock('volumes'):
                for volume in link['datasets']:
                    self.join_subtasks(self.run_subtask('volume.delete', volume))

        self.datastore.delete('replication.links', link['id'])

        remote_client = get_client(remote)
        if remote_client.call_sync('replication.link.get_one', name):
            remote_client.call_task_sync('replication.delete', name, scrub)
        remote_client.disconnect()

        self.dispatcher.dispatch_event('replication.changed', {
            'operation': 'delete',
            'ids': [link['id']]
        })


@description("Switch state of bi-directional replication link")
@accepts(str, h.ref('replication-link'))
class ReplicationUpdate(Task):
    def verify(self, name, updated_fields):
        if not self.datastore.exists('replication.links', ('name', '=', name)):
            raise VerifyException(errno.ENOENT, 'Bi-directional replication link {0} do not exist.'.format(name))

        return []

    def run(self, name, updated_fields):
        link = get_latest_bidir_link(self.dispatcher, self.datastore, name)
        is_master, remote = get_bidir_link_state(self.dispatcher, link)
        if 'update_date' not in updated_fields:
            link['update_date'] = str(datetime.utcnow())

        for partner in link['partners']:
            if partner != link['master']:
                link['master'] = partner

        self.datastore.update('replication.links', link['id'], link)

        self.dispatcher.dispatch_event('replication.changed', {
            'operation': 'update',
            'ids': [link['id']]
        })

        remote_client = get_client(remote)
        if link is not remote_client.call_sync('replication.link.get_one', name):
            remote_client.call_task_sync(
                'replication.update',
                link['name'],
                updated_fields
            )
        remote_client.disconnect()

        is_master, remote = get_bidir_link_state(self.dispatcher, link)
        set_bidir_link_state(self.dispatcher, is_master, link['datasets'], True)


@description("Triggers replication in bi-directional replication")
@accepts(str)
class ReplicationSync(Task):
    def verify(self, name):
        if not self.datastore.exists('replication.links', ('name', '=', name)):
            raise VerifyException(errno.ENOENT, 'Bi-directional replication link {0} do not exist.'.format(name))

        link = self.datastore.get_one('replication.links', ('name', '=', name))

        return ['zpool:{0}'.format(p) for p in link['datasets']]

    def run(self, name):
        link = get_latest_bidir_link(self.dispatcher, self.datastore, name)
        is_master, remote = get_bidir_link_state(self.dispatcher, link)
        remote_client = get_client(remote)
        if is_master:
            with self.dispatcher.get_lock('volumes'):
                set_bidir_link_state(remote_client, True, link['datasets'], False)
                for volume in link['datasets']:
                    self.join_subtasks(self.run_subtask(
                        'replication.replicate_dataset',
                        volume,
                        volume,
                        {
                            'remote': remote,
                            'remote_dataset': volume,
                            'recursive': True
                        }
                    ))

                    if link['replicate_services']:
                        remote_client.call_task_sync('volume.autoimport', volume, 'containers')
                        remote_client.call_task_sync('volume.autoimport', volume, 'shares')

                set_bidir_link_state(remote_client, False, link['datasets'], True)
        else:
            remote_client.call_task_sync(
                'replication.sync',
                link['name']
            )

        remote_client.disconnect()
        self.dispatcher.dispatch_event('replication.changed', {
            'operation': 'update',
            'ids': [link['id']]
        })


@accepts(str, str, bool, str, str, bool)
@returns(str)
class SnapshotDatasetTask(Task):
    def verify(self, pool, dataset, recursive, lifetime, prefix='auto', replicable=False):
        if not self.dispatcher.call_sync('zfs.dataset.query', [('name', '=', dataset)], {'single': True}):
            raise VerifyException(errno.ENOENT, 'Dataset {0} not found'.format(dataset))

        return ['zfs:{0}'.format(dataset)]

    def run(self, pool, dataset, recursive, lifetime, prefix='auto', replicable=False):
        def is_expired(snapshot):
            match = AUTOSNAP_RE.match(snapshot['snapshot_name'])
            if not match:
                return False

            if snapshot['holds']:
                return False

            if match.group('prefix') != prefix:
                return False

            delta = to_timedelta(match.group('lifetime'))
            creation = parse_datetime(snapshot['properties.creation.value'])
            return creation + delta < datetime.utcnow()

        snapshots = list(filter(is_expired, wrap(self.dispatcher.call_sync('zfs.dataset.get_snapshots', dataset))))
        snapname = '{0}-{1:%Y%m%d.%H%M}-{2}'.format(prefix, datetime.utcnow(), lifetime)
        params = {'org.freenas:replicate': {'value': 'yes'}} if replicable else None
        base_snapname = snapname

        # Pick another name in case snapshot already exists
        for i in range(1, 99):
            if self.dispatcher.call_sync(
                'zfs.snapshot.query',
                [('name', '=', '{0}@{1}'.format(dataset, snapname))],
                {'count': True}
            ):
                snapname = '{0}-{1}'.format(base_snapname, i)
                continue

            break

        self.join_subtasks(
            self.run_subtask('zfs.create_snapshot', pool, dataset, snapname, recursive, params),
            self.run_subtask(
                'zfs.delete_multiple_snapshots',
                pool,
                dataset,
                list(map(lambda s: s['snapshot_name'], snapshots)),
                True
            )
        )


@description("Runs a replication task with the specified arguments")
#@accepts(h.all_of(
#    h.ref('autorepl'),
#    h.required(
#        'remote',
#        'remote_port',
#        'dedicateduser',
#        'cipher',
#        'localfs',
#        'remotefs',
#        'compression',
#        'bandlim',
#        'followdelete',
#        'recursive',
#    ),
#))

class ReplicateDatasetPullTask(ProgressTask):
    def verify(self, trans_info):
        logger.debug('ReplicateDatasetPullTask.verify()')
        localfs = trans_info['remotefs']
        return ['zfs:{0}'.format(localfs)]

    def run(self, trans_info):
        logger.debug('ReplicateDatasetPullTask.run()')
        logger.debug('trans_info = %s', str(trans_info))

        tcp_ctrl = ReplicationTcpTransportCtrl(self, 'PULL')
        tcp_ctrl.pull__replicate(trans_info)

class ReplicateDatasetTask(ProgressTask):
    def verify(self, pool, localds, options, dry_run=False, tcp_transport=False):
        logger.debug('ReplicateDatasetPushTask.verify()')
        return ['zfs:{0}'.format(localds)]

    def run(self, pool, localds, options, dry_run=False, tcp_transport=False):
        logger.debug('ReplicateDatasetPushTask.run()')

        remote = options['remote']
        remoteds = options['remote_dataset']
        followdelete = options.get('followdelete', False)
        recursive = options.get('recursive', False)
        lifetime = options.get('lifetime', '1y')

        tcp_ctrl = ReplicationTcpTransportCtrl(self, 'PUSH') if tcp_transport else None

        self.join_subtasks(self.run_subtask(
            'volume.snapshot_dataset',
            pool,
            localds,
            True,
            lifetime,
            'repl',
            True
        ))

        datasets = [localds]
        remote_datasets = []
        actions = []

        remote_client = get_client(options['remote'])

        def is_replicated(snapshot):
            if snapshot.get('properties.org\\.freenas:replicate.value') != 'yes':
                # Snapshot is not subject to replication
                return False

            return True

        def matches(pair):
            src, tgt = pair
            srcsnap = src['snapshot_name']
            tgtsnap = tgt['snapshot_name']
            return srcsnap == tgtsnap and src['properties.creation.rawvalue'] == tgt['properties.creation.rawvalue']

        if recursive:
            datasets = self.dispatcher.call_sync(
                'zfs.dataset.query',
                [('name', '~', '^{0}(/|$)'.format(localds))],
                {'select': 'name'}
            )

            remote_datasets = remote_client.call_sync(
                'zfs.dataset.query',
                [('name', '~', '^{0}(/|$)'.format(remoteds))],
                {'select': 'name'}
            )

        self.set_progress(0, 'Reading replication state from remote side...')

        for ds in datasets:
            localfs = ds
            remotefs = localfs.replace(localds, remoteds, 1)
            local_snapshots = list(filter(
                is_replicated,
                wrap(self.dispatcher.call_sync('zfs.dataset.get_snapshots', localfs))
            ))

            try:
                remote_snapshots_full = wrap(
                    remote_client.call_sync(
                        'zfs.dataset.get_snapshots',
                        remotefs
                    )
                )
                remote_snapshots = list(filter(is_replicated, remote_snapshots_full))
            except RpcException as err:
                if err.code == errno.ENOENT:
                    # Dataset not found on remote side
                    remote_snapshots_full = None
                else:
                    raise TaskException(err.code, 'Cannot contact {0}: {1}'.format(remote, err.message))

            snapshots = local_snapshots[:]
            found = None

            if remote_snapshots_full:
                # Find out the last common snapshot.
                pairs = list(filter(matches, zip(local_snapshots, remote_snapshots)))
                if pairs:
                    pairs.sort(key=lambda p: int(p[0]['properties.creation.rawvalue']), reverse=True)
                    found, _ = first_or_default(None, pairs)

                if found:
                    if followdelete:
                        delete = []
                        for snap in remote_snapshots:
                            rsnap = snap['snapshot_name']
                            if not first_or_default(lambda s: s['snapshot_name'] == rsnap, local_snapshots):
                                delete.append(rsnap)

                        actions.append(ReplicationAction(
                            ReplicationActionType.DELETE_SNAPSHOTS,
                            localfs,
                            remotefs,
                            snapshots=delete
                        ))

                    index = local_snapshots.index(found)

                    for idx in range(index + 1, len(local_snapshots)):
                        actions.append(ReplicationAction(
                            ReplicationActionType.SEND_STREAM,
                            localfs,
                            remotefs,
                            incremental=True,
                            anchor=local_snapshots[idx - 1]['snapshot_name'],
                            snapshot=local_snapshots[idx]['snapshot_name']
                        ))
                else:
                    actions.append(ReplicationAction(
                        ReplicationActionType.DELETE_SNAPSHOTS,
                        localfs,
                        remotefs,
                        snapshots=map(lambda s: s['snapshot_name'], remote_snapshots_full)
                    ))

                    for idx in range(0, len(snapshots)):
                        actions.append(ReplicationAction(
                            ReplicationActionType.SEND_STREAM,
                            localfs,
                            remotefs,
                            incremental=idx > 0,
                            anchor=snapshots[idx - 1]['snapshot_name'] if idx > 0 else None,
                            snapshot=snapshots[idx]['snapshot_name']
                        ))
            else:
                logger.info('New dataset {0} -> {1}:{2}'.format(localfs, remote, remotefs))
                for idx in range(0, len(snapshots)):
                    actions.append(ReplicationAction(
                        ReplicationActionType.SEND_STREAM,
                        localfs,
                        remotefs,
                        incremental=idx > 0,
                        anchor=snapshots[idx - 1]['snapshot_name'] if idx > 0 else None,
                        snapshot=snapshots[idx]['snapshot_name']
                    ))

        for rds in remote_datasets:
            remotefs = rds
            localfs = remotefs.replace(remoteds, localds, 1)

            if localfs not in datasets:
                actions.append(ReplicationAction(
                    ReplicationActionType.DELETE_DATASET,
                    localfs,
                    remotefs
                ))

        # 1st pass - estimate send size
        self.set_progress(0, 'Estimating send size...')
        total_send_size = 0
        done_send_size = 0

        for action in actions:
            if action.type == ReplicationActionType.SEND_STREAM:
                size = self.dispatcher.call_sync(
                    'zfs.dataset.estimate_send_size',
                    action.localfs,
                    action.snapshot,
                    getattr(action, 'anchor', None)
                )

                action.send_size = size
                total_send_size += size

        if dry_run:
            return actions

        local_trans_infos, remote_trans_infos = tcp_ctrl.push__prepare_transaction_infos(actions) if tcp_transport else ([],[])
        tcp_ctrl.push__start_tcp_server_thread(local_trans_infos) if tcp_transport else None

        # 2nd pass - actual send
        for idx, action in enumerate(actions):
            progress = float(idx) / len(actions) * 100

            if action.type == ReplicationActionType.DELETE_SNAPSHOTS:
                self.set_progress(progress, 'Removing snapshots on remote dataset {0}'.format(action.remotefs))
                # Remove snapshots on remote side
                result = remote_client.call_task_sync(
                    'zfs.delete_multiple_snapshots',
                    action.remotefs.split('/')[0],
                    action.remotefs,
                    list(action.snapshots)
                )

                if result['state'] != 'FINISHED':
                    raise TaskException(errno.EFAULT, 'Failed to destroy snapshots on remote end: {0}'.format(
                        result['error']['message']
                    ))

            if action.type == ReplicationActionType.SEND_STREAM:
                self.set_progress(progress, 'Sending {0} stream of snapshot {1}/{2}'.format(
                    'incremental' if action.incremental else 'full',
                    action.localfs,
                    action.snapshot
                ))

                if not action.incremental:
                    send_dataset(
                        remote, 
                        options.get('remote_hostkey'), 
                        None, 
                        action.snapshot, 
                        action.localfs, 
                        action.remotefs, 
                        '', 
                        0, 
                        remote_trans_infos[idx] if remote_trans_infos else None, 
                        tcp_ctrl if tcp_transport else None,
                        tcp_transport,
                    )
                else:
                    send_dataset(
                        remote, 
                        options.get('remote_hostkey'), 
                        action.anchor, 
                        action.snapshot, 
                        action.localfs, 
                        action.remotefs, 
                        '', 
                        0, 
                        remote_trans_infos[idx] if remote_trans_infos else None,
                        tcp_ctrl if tcp_transport else None,
                        tcp_transport,
                    )
            if action.type == ReplicationActionType.DELETE_DATASET:
                self.set_progress(progress, 'Removing remote dataset {0}'.format(action.remotefs))
                result = remote_client.call_task_sync(
                    'zfs.destroy',
                    action.remotefs.split('/')[0],
                    action.remotefs
                )

                if result['state'] != 'FINISHED':
                    raise TaskException(errno.EFAULT, 'Failed to destroy dataset {0} on remote end: {1}'.format(
                        action.remotefs,
                        result['error']['message']
                    ))

        remote_client.disconnect()

        return actions


#
# Attempt to send a snapshot or increamental stream to remote.
#
def send_dataset(remote, hostkey, fromsnap, tosnap, dataset, remotefs, compression, throttle, trans_info=None, tcp_ctrl=None, tcp_transport=False):
    if (tcp_transport):
        # Transport layer for snapshot data is TCP
        tcp_ctrl.push__initiate_replication_rpc(remote, trans_info)
    else:
        # Transport layer for snapshot data is SSH
        send_dataset_over_ssh(remote, hostkey, fromsnap, tosnap, dataset, remotefs, compression, throttle)

def send_dataset_over_ssh(remote, hostkey, fromsnap, tosnap, dataset, remotefs, compression, throttle):
    zfs = sendzfs.SendZFS()
    zfs.send(remote, hostkey, fromsnap, tosnap, dataset, remotefs, compression, throttle, 1024*1024, None)

def get_client(remote):
    with open('/etc/replication/key') as f:
        pkey = RSAKey.from_private_key(f)

    try:
        remote_client = Client()
        remote_client.connect('ws+ssh://{0}'.format(remote), pkey=pkey)
        remote_client.login_service('replicator')
        return remote_client

    except AuthenticationException:
        raise RpcException(errno.EAUTH, 'Cannot connect to {0}'.format(remote))


def get_latest_bidir_link(dispatcher, datastore, name):
    if datastore.exists('replication.links', ('name', '=', name)):
        local_link = datastore.get_one('replication.links', ('name', '=', name))
        ips = dispatcher.call_sync('network.config.get_my_ips')
        remote = ''
        client = None
        for partner in local_link['partners']:
            if partner.split('@', 1)[1] not in ips:
                remote = partner

        try:
            client = get_client(remote)
            remote_link = client.call_sync('replication.link.get_one', name)
            client.disconnect()
            if not remote_link:
                return local_link

            if parse_datetime(local_link['update_date']) > parse_datetime(remote_link['update_date']):
                return local_link
            else:
                return remote_link

        except RpcException:
            if client:
                client.disconnect()
            return local_link

    else:
        return None


def get_bidir_link_state(dispatcher, link):
    is_master = False
    remote = ''
    ips = dispatcher.call_sync('network.config.get_my_ips')
    for ip in ips:
        for partner in link['partners']:
            if partner.endswith(ip) and partner == link['master']:
                is_master = True
    for partner in link['partners']:
        if partner.split('@', 1)[1] not in ips:
            remote = partner

    return is_master, remote


def set_bidir_link_state(client, enabled, datasets, set_services):
    for volume in datasets:
        if set_services:
            client.call_task_sync(
                'zfs.update',
                volume, volume,
                {'readonly': {'value': 'off'}}
            )
            vol_path = client.call_sync('volume.get_dataset_path', volume)
            vol_shares = client.call_sync('share.get_related', vol_path)
            vol_containers = client.call_sync('container.query', [('target', '=', volume)])
            for share in vol_shares:
                client.call_task_sync('share.update', share['id'], {'enabled': enabled})
            for container in vol_containers:
                client.call_task_sync('container.update', container['id'], {'enabled': enabled})
        client.call_task_sync(
            'zfs.update',
            volume, volume,
            {'readonly': {'value': 'off' if enabled else 'on'}}
        )


def _init(dispatcher, plugin):
    plugin.register_schema_definition('replication', {
        'type': 'object',
        'properties': {
            'remote': {'type': 'string'},
            'remote_port': {'type': 'string'},
            'remote_hostkey': {'type': 'string'},
            'remote_dataset': {'type': 'string'},
            'cipher': {
                'type': 'string',
                'enum': ['NORMAL', 'FAST', 'DISABLED']
            },
            'compression': {
                'type': 'string',
                'enum': ['none', 'pigz', 'plzip', 'lz4', 'xz']
            },
            'bandwidth_limit': {'type': 'string'},
            'followdelete': {'type': 'boolean'},
            'recursive': {'type': 'boolean'},
        },
        'additionalProperties': False,
    })

    plugin.register_schema_definition('replication-link', {
        'type': 'object',
        'properties': {
            'id': {'type': 'string'},
            'name': {'type': 'string'},
            'partners': {
                'type': 'array',
                'items': {'type': 'string'}
            },
            'master': {'type': 'string'},
            'update_date': {'type': 'string'},
            'datasets': {
                'type': 'array',
                'items': {'type': 'string'}
            },
            'bidirectional': {'type': 'boolean'},
            'replicate_services': {'type': 'boolean'},
            'recursive': {'type': 'boolean'}
        },
        'additionalProperties': False,
    })

    plugin.register_provider('replication', ReplicationProvider)
    plugin.register_provider('replication.link', ReplicationLinkProvider)
    plugin.register_task_handler('volume.snapshot_dataset', SnapshotDatasetTask)
    plugin.register_task_handler('replication.scan_hostkey', ScanHostKeyTask)
    plugin.register_task_handler('replication.replicate_dataset', ReplicateDatasetTask)
    plugin.register_task_handler('replication.replicate_dataset_pull', ReplicateDatasetPullTask)
    plugin.register_task_handler('replication.create', ReplicationCreate)
    plugin.register_task_handler('replication.update', ReplicationUpdate)
    plugin.register_task_handler('replication.sync', ReplicationSync)
    plugin.register_task_handler('replication.delete', ReplicationDelete)

    plugin.register_event_type('replication.changed')

    # Generate replication key pair on first run
    if not dispatcher.configstore.get('replication.key.private') or not dispatcher.configstore.get('replication.key.public'):
        key = RSAKey.generate(bits=2048)
        buffer = io.StringIO()
        key.write_private_key(buffer)
        dispatcher.configstore.set('replication.key.private', buffer.getvalue())
        dispatcher.configstore.set('replication.key.public', key.get_base64())

    def on_etcd_resume(args):
        if args.get('name') != 'etcd.generation':
            return

        dispatcher.call_sync('etcd.generation.generate_group', 'replication')

    plugin.register_event_handler('plugin.service_resume', on_etcd_resume)
