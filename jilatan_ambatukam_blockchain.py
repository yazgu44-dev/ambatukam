#!/usr/bin/env python3
import hashlib
import hmac
import ipaddress
import json
import math
import mmap
import multiprocessing as mp
import os
import platform
import re
import secrets
import signal
import socket
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import deque
from decimal import Decimal, InvalidOperation
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from multiprocessing.connection import wait
from urllib.parse import parse_qs, urlparse

NAME = 'Jilatan Ambatukam Blockchain'
SYMBOL = 'JAB'
VERSION = '1.01'
UNIT = 10 ** 8
MAX_SUPPLY = 30000000 * UNIT
INITIAL_REWARD = 50 * UNIT
HALVING = 300000
TARGET_TIME = 10
ADJUST = 10
INITIAL_DIFFICULTY = 20.0
MAX_TARGET = 2 ** 240
HASHES_PER_DIFF = 65536

COINBASE_MATURITY = 5
MIN_FEE = 1000
DUST = 546
MAX_BLOCK_TXS = 200
MAX_MEMPOOL = 1000
MAX_FUTURE_MS = 2 * 60 * 1000
SYNC_EVERY = 8
STATUS_EVERY = 10

MAX_REORG = 100
MAX_PEERS = 16
MAX_CONNECTIONS = 48
MAX_TX_SIZE = 100000
MAX_BODY = {'/api/block': 2 * 1024 * 1024, '/api/tx': 128 * 1024}
RATE = {'read': 300, 'tx': 60, 'block': 30, 'hello': 6, 'admin': 20}
BAN_SCORE = 100
BAN_SECONDS = 600
FETCH_BLOCKS = 50
SEEDS = []

P = 2 ** 256 - 2 ** 32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (GX, GY)


def sha256_hex(data):
    return hashlib.sha256(data).hexdigest()


def sha256d(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def point_add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        slope = 3 * a[0] * a[0] * pow(2 * a[1], -1, P) % P
    else:
        slope = (b[1] - a[1]) * pow(b[0] - a[0], -1, P) % P
    x = (slope * slope - a[0] - b[0]) % P
    return (x, (slope * (a[0] - x) - a[1]) % P)


def point_mul(k, point):
    result = None
    while k:
        if k & 1:
            result = point_add(result, point)
        point = point_add(point, point)
        k >>= 1
    return result


def address_of(public_hex):
    try:
        return 'JAB' + sha256_hex(bytes.fromhex(public_hex))[:40]
    except (ValueError, TypeError):
        return None


def is_valid_address(address):
    return isinstance(address, str) and re.fullmatch(r'JAB[0-9a-f]{40}', address) is not None and '911' in address


def create_wallet():
    while True:
        private = secrets.randbelow(N - 1) + 1
        x, y = point_mul(private, G)
        public = b'\x04' + x.to_bytes(32, 'big') + y.to_bytes(32, 'big')
        address = 'JAB' + sha256_hex(public)[:40]
        if '911' in address:
            return {'privateKey': '%064x' % private, 'publicKey': public.hex(), 'address': address}


def sign(private_hex, message_hex):
    d = int(private_hex, 16)
    z = int(message_hex, 16) % N
    key = bytes.fromhex(private_hex)
    counter = 0
    while True:
        seed = bytes.fromhex(message_hex) + counter.to_bytes(4, 'big')
        k = int.from_bytes(hmac.new(key, seed, 'sha256').digest(), 'big') % N
        counter += 1
        if k == 0:
            continue
        r = point_mul(k, G)[0] % N
        s = pow(k, -1, N) * (z + r * d) % N
        if r == 0 or s == 0:
            continue
        if s > N // 2:
            s = N - s
        return '%064x%064x' % (r, s)


VERIFIED = set()


def verify(public_hex, message_hex, sig_hex):
    key = (public_hex, message_hex, sig_hex)
    if key in VERIFIED:
        return True
    try:
        pub = bytes.fromhex(public_hex)
        sig = bytes.fromhex(sig_hex)
        z = int(message_hex, 16) % N
    except (ValueError, TypeError):
        return False
    if len(pub) != 65 or pub[0] != 4 or len(sig) != 64:
        return False
    x = int.from_bytes(pub[1:33], 'big')
    y = int.from_bytes(pub[33:], 'big')
    if x >= P or y >= P or (y * y - x * x * x - 7) % P:
        return False
    r = int.from_bytes(sig[:32], 'big')
    s = int.from_bytes(sig[32:], 'big')
    if not (0 < r < N and 0 < s < N):
        return False
    w = pow(s, -1, N)
    point = point_add(point_mul(z * w % N, G), point_mul(r * w % N, (x, y)))
    ok = point is not None and point[0] % N == r
    if ok:
        if len(VERIFIED) > 50000:
            VERIFIED.clear()
        VERIFIED.add(key)
    return ok


def target_for(difficulty):
    return (MAX_TARGET * 1000000 // max(1, int(difficulty * 1000000))).to_bytes(32, 'big')


def fmt_amount(units):
    text = ('%.8f' % (units / UNIT)).rstrip('0').rstrip('.')
    return text or '0'


def parse_amount(value):
    try:
        number = Decimal(str(value).strip().replace(',', '.'))
    except (InvalidOperation, ValueError):
        raise ValueError('jumlah tidak valid')
    if not number.is_finite() or number <= 0:
        raise ValueError('jumlah harus lebih dari 0')
    units = number * UNIT
    if units != units.to_integral_value():
        raise ValueError('maksimal 8 angka di belakang koma')
    if units > MAX_SUPPLY:
        raise ValueError('jumlah melebihi suplai maksimum')
    return int(units)


def tx_id(tx):
    body = {
        'in': [[i['txid'], i['vout']] for i in tx['inputs']],
        'out': [[o['address'], o['amount']] for o in tx['outputs']],
        'cb': tx.get('coinbase'),
    }
    return sha256_hex(json.dumps(body, separators=(',', ':')).encode())


def merkle_root(ids):
    layer = [bytes.fromhex(i) for i in ids]
    if not layer:
        return '0' * 64
    while len(layer) > 1:
        if len(layer) % 2:
            layer.append(layer[-1])
        layer = [sha256d(layer[i] + layer[i + 1]) for i in range(0, len(layer), 2)]
    return layer[0].hex()


GENESIS = {
    'index': 0,
    'prevHash': '0' * 64,
    'timestamp': 1767225600000,
    'difficulty': INITIAL_DIFFICULTY,
    'miner': 'genesis',
    'reward': 0,
    'nonce': 0,
    'hash': sha256_hex(b'Jilatan Ambatukam Blockchain genesis'),
}


def prefix_of(block):
    if 'merkleRoot' in block:
        return '%d|%s|%d|%s|%s|%d|%s|' % (
            block['index'], block['prevHash'], block['timestamp'], repr(float(block['difficulty'])),
            block['miner'], block['reward'], block['merkleRoot'])
    return '%d|%s|%d|%s|%s|%d|' % (
        block['index'], block['prevHash'], block['timestamp'], repr(float(block['difficulty'])),
        block['miner'], block['reward'])


def coinbase_for(block):
    tx = {'coinbase': block['index'], 'inputs': [],
          'outputs': [{'address': block['miner'], 'amount': block['reward']}]}
    tx['id'] = tx_id(tx)
    return tx


def block_txs(block):
    if block.get('txs'):
        return block['txs']
    return [coinbase_for(block)] if block['index'] > 0 else []


HEX64 = re.compile(r'[0-9a-f]{64}')
HEX_ANY = re.compile(r'[0-9a-fA-F]+')


def clean_tx(tx):
    if not isinstance(tx, dict):
        raise ValueError('invalid transaction')
    result = {}
    if tx.get('coinbase') is not None:
        if type(tx['coinbase']) is not int:
            raise ValueError('invalid transaction')
        result['coinbase'] = tx['coinbase']
    inputs, outputs = tx['inputs'], tx['outputs']
    if not isinstance(inputs, list) or not isinstance(outputs, list) or len(inputs) > 100 or len(outputs) > 100:
        raise ValueError('invalid transaction size')
    result['inputs'] = []
    for item in inputs:
        txid, pub, sig = item['txid'], item['pubkey'], item['sig']
        if (type(item['vout']) is not int or not isinstance(txid, str) or not HEX64.fullmatch(txid)
                or not isinstance(pub, str) or len(pub) != 130 or not HEX_ANY.fullmatch(pub)
                or not isinstance(sig, str) or len(sig) != 128 or not HEX_ANY.fullmatch(sig)):
            raise ValueError('invalid input')
        result['inputs'].append({'txid': txid, 'vout': item['vout'], 'pubkey': pub, 'sig': sig})
    result['outputs'] = []
    for out in outputs:
        if not isinstance(out['address'], str) or type(out['amount']) is not int:
            raise ValueError('invalid output')
        result['outputs'].append({'address': out['address'], 'amount': out['amount']})
    if not isinstance(tx['id'], str) or not HEX64.fullmatch(tx['id']):
        raise ValueError('invalid txid')
    result['id'] = tx['id']
    return result


def clean_block(block):
    if not isinstance(block, dict):
        raise ValueError('malformed block')
    result = {}
    for key in ('index', 'timestamp', 'reward', 'nonce'):
        if type(block[key]) is not int:
            raise ValueError('malformed block')
        result[key] = block[key]
    for key in ('prevHash', 'miner', 'hash'):
        if not isinstance(block[key], str) or len(block[key]) > 100:
            raise ValueError('malformed block')
        result[key] = block[key]
    difficulty = block['difficulty']
    if type(difficulty) not in (int, float) or not math.isfinite(difficulty):
        raise ValueError('malformed block')
    result['difficulty'] = difficulty
    if 'merkleRoot' in block:
        if not isinstance(block['merkleRoot'], str) or len(block['merkleRoot']) > 100:
            raise ValueError('malformed block')
        result['merkleRoot'] = block['merkleRoot']
        txs = block['txs']
        if not isinstance(txs, list) or not txs or len(txs) > MAX_BLOCK_TXS + 1:
            raise ValueError('invalid transaction count')
        result['txs'] = [clean_tx(tx) for tx in txs]
    return result


def supply_at(index):
    total, era, remaining = 0, 0, index
    while remaining > 0 and era < 40:
        count = min(remaining, HALVING)
        total += count * (INITIAL_REWARD >> era)
        remaining -= count
        era += 1
    return min(total, MAX_SUPPLY)


class Chain:
    def __init__(self, directory=None, reverify=False):
        self.file = None
        self.loading = False
        self.lock = threading.RLock()
        self.reset()
        if not directory:
            return
        os.makedirs(directory, exist_ok=True)
        self.file = os.path.join(directory, 'blocks.ndjson')
        if not os.path.exists(self.file):
            return
        damaged = False
        self.loading = not reverify
        try:
            with open(self.file) as handle:
                for line in handle:
                    if not line.strip():
                        continue
                    try:
                        self.add_block(json.loads(line), persist=False, check_time=False)
                    except ValueError as error:
                        print('Peringatan: file blok rusak di blok #%d (%s), sisanya dibuang.' % (len(self.blocks), error))
                        damaged = True
                        break
        finally:
            self.loading = False
        if damaged:
            self.rewrite()

    def reset(self):
        self.blocks = [GENESIS]
        self.supply = 0
        self.work = 0.0
        self.utxo = {}
        self.balances = {}
        self.by_addr = {}
        self.tx_height = {}
        self.addr_txs = {}
        self.tx_total = 0
        self.fees_total = 0
        self.received = {}
        self.sent = {}
        self.mined = {}

    @property
    def tip(self):
        return self.blocks[-1]

    def next_reward(self):
        era = (len(self.blocks) - 1) // HALVING
        if era >= 40:
            return 0
        return max(0, min(INITIAL_REWARD >> era, MAX_SUPPLY - self.supply))

    def next_difficulty(self):
        height = len(self.blocks)
        last = self.tip
        if height % ADJUST:
            return last['difficulty']
        first = self.blocks[height - ADJUST + 1]
        actual = max(1, (last['timestamp'] - first['timestamp']) / 1000)
        ratio = min(4, max(0.25, (ADJUST - 2) * TARGET_TIME / actual))
        return max(1.0, round(last['difficulty'] * ratio, 3))

    def check_tx(self, tx, spent, created, height):
        if not isinstance(tx, dict) or tx.get('coinbase') is not None:
            raise ValueError('invalid transaction')
        inputs, outputs = tx['inputs'], tx['outputs']
        if not inputs or not outputs or len(inputs) > 100 or len(outputs) > 100:
            raise ValueError('invalid transaction size')
        txid = tx_id(tx)
        if tx.get('id') != txid:
            raise ValueError('invalid txid')
        total_in = 0
        for item in inputs:
            if type(item['vout']) is not int:
                raise ValueError('invalid vout')
            key = (item['txid'], item['vout'])
            if key in spent:
                raise ValueError('double spend')
            entry = created.get(key) or self.utxo.get(key)
            if entry is None:
                raise ValueError('input not found')
            address, amount, born, coinbase = entry
            if coinbase and height - born < COINBASE_MATURITY:
                raise ValueError('coinbase not mature')
            if address_of(item['pubkey']) != address:
                raise ValueError('pubkey does not match address')
            if not self.loading and not verify(item['pubkey'], txid, item['sig']):
                raise ValueError('invalid signature')
            spent.add(key)
            total_in += amount
        total_out = 0
        for out in outputs:
            if not is_valid_address(out['address']) or type(out['amount']) is not int or out['amount'] < DUST:
                raise ValueError('invalid output')
            total_out += out['amount']
        if total_out > total_in:
            raise ValueError('outputs exceed inputs')
        for n, out in enumerate(outputs):
            created[(txid, n)] = (out['address'], out['amount'], height, False)
        return total_in - total_out

    def add_block(self, block, persist=True, check_time=True):
        with self.lock:
            try:
                block = clean_block(block)
                self._add_block(block, persist, check_time)
                return block
            except (KeyError, TypeError, AttributeError, IndexError):
                raise ValueError('malformed block')

    def _add_block(self, block, persist, check_time):
        tip = self.tip
        index = block['index']
        if index != tip['index'] + 1 or block['prevHash'] != tip['hash']:
            raise ValueError('invalid link')
        if block['timestamp'] < tip['timestamp']:
            raise ValueError('invalid timestamp')
        if check_time and block['timestamp'] > time.time() * 1000 + MAX_FUTURE_MS:
            raise ValueError('timestamp too far ahead')
        if not is_valid_address(block['miner']):
            raise ValueError('invalid miner address')
        if block['difficulty'] != self.next_difficulty():
            raise ValueError('invalid difficulty')
        if block['reward'] != self.next_reward():
            raise ValueError('invalid reward')
        if type(block['nonce']) is not int:
            raise ValueError('invalid nonce')
        digest = hashlib.sha256((prefix_of(block) + str(block['nonce'])).encode()).digest()
        if digest.hex() != block['hash'] or digest > target_for(block['difficulty']):
            raise ValueError('invalid proof of work')

        spent, created = set(), {}
        fees = 0
        if 'merkleRoot' in block:
            txs = block['txs']
            if not txs or len(txs) > MAX_BLOCK_TXS + 1:
                raise ValueError('invalid transaction count')
            coinbase = txs[0]
            if coinbase.get('coinbase') != index or coinbase['inputs'] or coinbase.get('id') != tx_id(coinbase):
                raise ValueError('invalid coinbase')
            ids = [coinbase['id']]
            fees = 0
            for tx in txs[1:]:
                fees += self.check_tx(tx, spent, created, index)
                ids.append(tx['id'])
            outs = coinbase['outputs']
            if len(outs) != 1 or outs[0]['address'] != block['miner'] or outs[0]['amount'] != block['reward'] + fees:
                raise ValueError('invalid coinbase amount')
            if len(set(ids)) != len(ids) or block['merkleRoot'] != merkle_root(ids):
                raise ValueError('invalid merkle root')
            all_txs = txs
        else:
            if 'merkleRoot' in tip:
                raise ValueError('old block format after upgrade')
            coinbase = coinbase_for(block)
            all_txs = [coinbase]
        if coinbase['outputs'][0]['amount'] > 0:
            created[(coinbase['id'], 0)] = (block['miner'], coinbase['outputs'][0]['amount'], index, True)

        for tx in all_txs:
            touched = {o['address'] for o in tx['outputs']} | {address_of(i['pubkey']) for i in tx['inputs']}
            for address in touched:
                self.addr_txs.setdefault(address, []).append((index, tx['id']))
            self.tx_height[tx['id']] = index
            incoming, outgoing = {}, {}
            for item in tx['inputs']:
                key = (item['txid'], item['vout'])
                entry = created.get(key) or self.utxo.get(key)
                outgoing[entry[0]] = outgoing.get(entry[0], 0) + entry[1]
            for out in tx['outputs']:
                incoming[out['address']] = incoming.get(out['address'], 0) + out['amount']
            for address in set(incoming) | set(outgoing):
                net = incoming.get(address, 0) - outgoing.get(address, 0)
                if net > 0:
                    self.received[address] = self.received.get(address, 0) + net
                elif net < 0:
                    self.sent[address] = self.sent.get(address, 0) - net
        record = self.mined.setdefault(block['miner'], {'count': 0, 'amount': 0, 'heights': []})
        record['count'] += 1
        record['amount'] += coinbase['outputs'][0]['amount']
        record['heights'].append(index)
        if len(record['heights']) > 50:
            del record['heights'][0]
        self.tx_total += len(all_txs) - 1
        self.fees_total += fees
        for key in spent:
            created.pop(key, None)
            entry = self.utxo.pop(key, None)
            if entry:
                self.balances[entry[0]] -= entry[1]
                self.by_addr[entry[0]].discard(key)
        for key, entry in created.items():
            self.utxo[key] = entry
            self.balances[entry[0]] = self.balances.get(entry[0], 0) + entry[1]
            self.by_addr.setdefault(entry[0], set()).add(key)
        self.blocks.append(block)
        self.supply += block['reward']
        self.work += block['difficulty']
        if persist and self.file:
            with open(self.file, 'a') as handle:
                handle.write(json.dumps(block) + '\n')
                handle.flush()
                os.fsync(handle.fileno())

    @staticmethod
    def replay(blocks):
        other = Chain(None)
        other.loading = True
        for block in blocks[1:]:
            other.add_block(block, persist=False, check_time=False)
        other.loading = False
        return other

    def rewrite(self):
        if not self.file:
            return
        temp = self.file + '.tmp'
        with open(temp, 'w') as handle:
            for block in self.blocks[1:]:
                handle.write(json.dumps(block) + '\n')
        os.replace(temp, self.file)

    def adopt(self, other):
        with self.lock:
            for name in ('blocks', 'supply', 'work', 'utxo', 'balances', 'by_addr', 'tx_height', 'addr_txs',
                         'tx_total', 'fees_total', 'received', 'sent', 'mined'):
                setattr(self, name, getattr(other, name))
            self.rewrite()

    def get_block(self, ident):
        with self.lock:
            if re.fullmatch(r'\d+', ident):
                index = int(ident)
                return self.blocks[index] if index < len(self.blocks) else None
            for block in reversed(self.blocks):
                if block['hash'] == ident:
                    return block
            return None

    def get_tx(self, txid):
        height = self.tx_height.get(txid)
        if height is None:
            return None
        for tx in block_txs(self.blocks[height]):
            if tx['id'] == txid:
                return tx, height
        return None

    def spendable_utxos(self, address):
        height = len(self.blocks)
        coins = []
        for key in self.by_addr.get(address, ()):
            _, amount, born, coinbase = self.utxo[key]
            if not coinbase or height - born >= COINBASE_MATURITY:
                coins.append((key, amount))
        return coins

    def describe(self, tx, height=None):
        inputs, total_in = [], 0
        for item in tx['inputs']:
            found = self.get_tx(item['txid'])
            amount = found[0]['outputs'][item['vout']]['amount'] if found else 0
            inputs.append({'txid': item['txid'], 'vout': item['vout'],
                           'address': address_of(item['pubkey']), 'amount': amount / UNIT})
            total_in += amount
        total_out = sum(o['amount'] for o in tx['outputs'])
        coinbase = tx.get('coinbase') is not None
        return {
            'id': tx['id'], 'coinbase': coinbase, 'height': height,
            'confirmations': self.tip['index'] - height + 1 if height is not None else 0,
            'timestamp': self.blocks[height]['timestamp'] if height is not None else None,
            'size': len(json.dumps(tx)),
            'inputs': inputs,
            'outputs': [{'address': o['address'], 'amount': o['amount'] / UNIT} for o in tx['outputs']],
            'total': total_out / UNIT,
            'fee': 0 if coinbase else (total_in - total_out) / UNIT,
        }

    def interval_of(self, block):
        index = block['index']
        if index < 2 or index >= len(self.blocks):
            return None
        return (block['timestamp'] - self.blocks[index - 1]['timestamp']) / 1000

    def brief(self, block):
        txs = block_txs(block)
        fees = txs[0]['outputs'][0]['amount'] - block['reward'] if txs else 0
        return {'index': block['index'], 'hash': block['hash'], 'prevHash': block['prevHash'],
                'miner': block['miner'], 'reward': block['reward'] / UNIT, 'difficulty': block['difficulty'],
                'timestamp': block['timestamp'], 'transfers': max(0, len(txs) - 1), 'fees': fees / UNIT,
                'interval': self.interval_of(block)}

    def block_detail(self, block):
        with self.lock:
            data = self.brief(block)
            raw = block_txs(block)
            moved = sum(o['amount'] for tx in raw[1:] for o in tx['outputs'])
            data.update({'nonce': block['nonce'], 'merkleRoot': block.get('merkleRoot'),
                         'confirmations': self.tip['index'] - block['index'] + 1,
                         'size': len(json.dumps(block)),
                         'txCount': len(raw),
                         'volume': moved / UNIT,
                         'claimed': raw[0]['outputs'][0]['amount'] / UNIT if raw else 0,
                         'target': target_for(block['difficulty']).hex(),
                         'estimatedHashes': block['difficulty'] * HASHES_PER_DIFF,
                         'supplyAfter': supply_at(block['index']) / UNIT,
                         'format': 'v2' if 'merkleRoot' in block else 'v1'})
            txs = [self.describe(tx, block['index']) for tx in raw]
            return {'block': data, 'txs': txs}

    def chart(self, limit):
        with self.lock:
            items = []
            for i in range(max(1, len(self.blocks) - limit), len(self.blocks)):
                block = self.blocks[i]
                items.append({'index': i, 'interval': self.interval_of(block), 'difficulty': block['difficulty'],
                              'transfers': max(0, len(block_txs(block)) - 1), 'timestamp': block['timestamp']})
            return items

    def address_info(self, address):
        if not is_valid_address(address):
            raise ValueError('alamat tidak valid')
        with self.lock:
            balance = self.balances.get(address, 0)
            spendable = sum(value for _, value in self.spendable_utxos(address))
            entries = self.addr_txs.get(address, [])
            history = []
            for height, txid in reversed(entries[-30:]):
                tx = self.get_tx(txid)[0]
                delta = sum(o['amount'] for o in tx['outputs'] if o['address'] == address)
                for item in tx['inputs']:
                    if address_of(item['pubkey']) == address:
                        delta -= self.get_tx(item['txid'])[0]['outputs'][item['vout']]['amount']
                history.append({'id': txid, 'height': height, 'timestamp': self.blocks[height]['timestamp'],
                                'delta': delta / UNIT, 'coinbase': tx.get('coinbase') is not None})
            mined = self.mined.get(address, {})
            return {'address': address, 'balance': balance / UNIT, 'spendable': spendable / UNIT,
                    'immature': (balance - spendable) / UNIT, 'txCount': len(entries), 'history': history,
                    'received': self.received.get(address, 0) / UNIT,
                    'sent': self.sent.get(address, 0) / UNIT,
                    'utxoCount': len(self.by_addr.get(address, ())),
                    'firstSeen': self.blocks[entries[0][0]]['timestamp'] if entries else None,
                    'lastSeen': self.blocks[entries[-1][0]]['timestamp'] if entries else None,
                    'minedBlocks': mined.get('count', 0),
                    'minedAmount': mined.get('amount', 0) / UNIT,
                    'supplyShare': balance / self.supply * 100 if self.supply else 0,
                    'rank': 1 + sum(1 for v in self.balances.values() if v > balance) if balance > 0 else None}

    def average_block_time(self):
        length = len(self.blocks)
        span = min(length - 2, ADJUST)
        if span < 1:
            return 0.0
        return (self.tip['timestamp'] - self.blocks[length - 1 - span]['timestamp']) / span / 1000

    def network_hashrate(self):
        average = self.average_block_time()
        return self.tip['difficulty'] * HASHES_PER_DIFF / average if average > 0 else 0.0

    def balance_of(self, address):
        return self.balances.get(address, 0) / UNIT

    def summary(self):
        with self.lock:
            height = self.tip['index']
            holders = sorted(((a, v) for a, v in self.balances.items() if v > 0), key=lambda item: -item[1])
            era = height // HALVING
            size = 0
            if self.file and os.path.exists(self.file):
                size = os.path.getsize(self.file)
            return {
                'genesis': GENESIS['hash'],
                'tip': self.tip['hash'],
                'totalWork': self.work,
                'totalHashes': self.work * HASHES_PER_DIFF,
                'totalTransfers': self.tx_total,
                'totalFees': self.fees_total / UNIT,
                'addresses': len(self.addr_txs),
                'utxoCount': len(self.utxo),
                'minerCount': len(self.mined),
                'dataSize': size,
                'era': era + 1,
                'nextHalvingHeight': (era + 1) * HALVING,
                'nextHalvingReward': (INITIAL_REWARD >> (era + 1)) / UNIT if era + 1 < 40 else 0,
                'blocksUntilAdjust': (ADJUST - (height + 1) % ADJUST) % ADJUST,
                'rules': {'targetBlockTime': TARGET_TIME, 'adjustEvery': ADJUST, 'halving': HALVING,
                          'minFee': MIN_FEE / UNIT, 'dust': DUST / UNIT, 'maturity': COINBASE_MATURITY,
                          'maxBlockTxs': MAX_BLOCK_TXS, 'maxMempool': MAX_MEMPOOL, 'maxReorg': MAX_REORG,
                          'initialReward': INITIAL_REWARD / UNIT, 'hashesPerDifficulty': HASHES_PER_DIFF},
                'name': NAME,
                'symbol': SYMBOL,
                'version': VERSION,
                'height': height,
                'difficulty': self.next_difficulty(),
                'reward': self.next_reward() / UNIT,
                'targetBlockTime': TARGET_TIME,
                'averageBlockTime': self.average_block_time(),
                'networkHashrate': self.network_hashrate(),
                'maxSupply': MAX_SUPPLY / UNIT,
                'circulatingSupply': self.supply / UNIT,
                'remainingSupply': (MAX_SUPPLY - self.supply) / UNIT,
                'supplyPercent': self.supply / MAX_SUPPLY * 100,
                'holders': len(holders),
                'blocksUntilHalving': (height // HALVING + 1) * HALVING - height,
                'topHolders': [{'address': a, 'balance': v / UNIT,
                                'share': v / self.supply * 100 if self.supply else 0} for a, v in holders[:10]],
                'recent': [self.brief(b) for b in reversed(self.blocks[-10:])],
            }


def worker(index, step, jobs, results, counters, parent):
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    job_id = None
    prefix = b''
    target = b''
    nonce = index
    sha = hashlib.sha256
    while True:
        if os.getppid() != parent:
            return
        message = None
        try:
            while jobs.poll():
                message = jobs.recv()
        except (EOFError, OSError):
            return
        if message is not None:
            job_id = message['id']
            prefix = message['prefix'].encode()
            target = bytes.fromhex(message['target'])
            nonce = index
        if job_id is None:
            time.sleep(0.02)
            continue
        done = 0
        for done in range(1, 20001):
            digest = sha(prefix + str(nonce).encode()).digest()
            if digest <= target:
                results.send((job_id, nonce, digest.hex()))
                job_id = None
                break
            nonce += step
        counters[index] += done


class Miner:
    def __init__(self, threads):
        self.threads = threads
        self.memory = mmap.mmap(-1, 8 * threads)
        self.counters = memoryview(self.memory).cast('Q')
        self.jobs, self.readers = [], []
        parent = os.getpid()
        for i in range(threads):
            job_read, job_write = mp.Pipe(duplex=False)
            result_read, result_write = mp.Pipe(duplex=False)
            mp.Process(target=worker, args=(i, threads, job_read, result_write, self.counters, parent),
                       daemon=True).start()
            job_read.close()
            result_write.close()
            self.jobs.append(job_write)
            self.readers.append(result_read)
        self.job = 0
        self.template = None
        self.rates = [0.0] * threads
        self.previous = [0] * threads
        self.last_time = time.time()
        self.mined = 0
        self.last = None
        self.stale = 0
        self.rejected = 0
        self.job_base = 0
        self.job_start = time.time()

    def total_hashes(self):
        return sum(self.counters)

    def set_job(self, block, txs):
        self.job += 1
        self.job_base = self.total_hashes()
        self.job_start = time.time()
        self.template = (block, txs)
        message = {'id': self.job, 'prefix': prefix_of(block), 'target': target_for(block['difficulty']).hex()}
        for pipe in self.jobs:
            try:
                pipe.send(message)
            except (OSError, ValueError):
                pass

    def sample(self):
        now = time.time()
        elapsed = max(0.001, now - self.last_time)
        current = list(self.counters)
        self.rates = [(current[i] - self.previous[i]) / elapsed for i in range(self.threads)]
        self.previous = current
        self.last_time = now


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


OPENER = urllib.request.build_opener(NoRedirect)
LOOPBACK = ('127.0.0.1', '::1', '::ffff:127.0.0.1')


def http_json(url, payload=None, timeout=6, headers=None):
    data = None if payload is None else json.dumps(payload).encode()
    head = {'Content-Type': 'application/json', 'User-Agent': 'JilatanAmbatukamNode/%s' % VERSION}
    head.update(headers or {})
    request = urllib.request.Request(url, data=data, headers=head,
                                     method='GET' if payload is None else 'POST')
    try:
        with OPENER.open(request, timeout=timeout) as response:
            return json.loads(response.read(8 * 1024 * 1024))
    except urllib.error.HTTPError as error:
        try:
            message = json.loads(error.read(65536)).get('error')
        except (ValueError, AttributeError):
            message = None
        raise ValueError(message or 'HTTP %d' % error.code)


def clean_url(url):
    url = str(url).strip().rstrip('/')
    if len(url) > 200:
        raise ValueError('alamat peer terlalu panjang')
    if not re.match(r'^https?://', url):
        url = 'http://' + url
    parsed = urlparse(url)
    if not parsed.hostname or parsed.username or parsed.password:
        raise ValueError('alamat peer tidak valid')
    parsed.port
    return '%s://%s' % (parsed.scheme, parsed.netloc)


def public_host(host):
    try:
        infos = socket.getaddrinfo(host, None)
    except OSError:
        return False
    if not infos:
        return False
    for info in infos:
        try:
            if not ipaddress.ip_address(info[4][0].split('%')[0]).is_global:
                return False
        except ValueError:
            return False
    return True


class BadPeer(Exception):
    pass


class SelfPeer(Exception):
    pass


def peer_error(error):
    text = str(error)
    return ValueError(text) if 'too far ahead' in text else BadPeer(text)


class Guard:
    def __init__(self):
        self.lock = threading.Lock()
        self.hits = {}
        self.score = {}
        self.banned = {}

    def is_banned(self, ip):
        with self.lock:
            return self.banned.get(ip, 0) > time.time()

    def allow(self, ip, bucket):
        now = time.time()
        with self.lock:
            if self.banned.get(ip, 0) > now:
                return False
            queue = self.hits.setdefault((ip, bucket), deque())
            while queue and queue[0] < now - 60:
                queue.popleft()
            if len(queue) >= RATE[bucket]:
                return False
            queue.append(now)
            if len(self.hits) > 5000:
                self.hits = {k: v for k, v in self.hits.items() if v and v[-1] > now - 60}
            if len(self.banned) > 5000:
                self.banned = {k: v for k, v in self.banned.items() if v > now}
            return True

    def strike(self, ip, points):
        now = time.time()
        with self.lock:
            score, at = self.score.get(ip, (0.0, now))
            score = max(0.0, score - (now - at) / 10) + points
            if score >= BAN_SCORE:
                self.banned[ip] = now + BAN_SECONDS
                self.score.pop(ip, None)
                return True
            if len(self.score) > 5000:
                self.score.clear()
            self.score[ip] = (score, now)
            return False


STYLE = {'on': sys.stdout.isatty() and 'NO_COLOR' not in os.environ}


def color(text, code):
    return '\033[%sm%s\033[0m' % (code, text) if STYLE['on'] else text


def dim(text):
    return color(text, '2')


def strip_ansi(text):
    return re.sub(r'\033\[[0-9;]*m', '', text)


def term_width():
    try:
        return max(48, min(78, os.get_terminal_size().columns))
    except OSError:
        return 72


def clock():
    return time.strftime('%H:%M:%S')


def log(tag, text, code='36'):
    style = code if ';' in code else '1;' + code
    print('%s %s %s' % (dim(clock()), color('%-8s' % tag, style), text), flush=True)


def heading(left, right=''):
    gap = max(2, term_width() - len(strip_ansi(left)) - len(strip_ansi(right)) - 6)
    return '  %s %s %s' % (left, dim('━' * gap), right)


def section(title):
    return '\n  %s %s' % (color(title, '1;33'), dim('─' * max(4, term_width() - len(title) - 6)))


def kv(label, value, width=14):
    return '    %s %s' % (dim(label.ljust(width)), value)


def gauge(fraction, size=24):
    fraction = max(0.0, min(1.0, fraction))
    filled = int(round(fraction * size))
    return color('█' * filled, '33') + dim('░' * (size - filled))


def spark(values):
    bars = '▁▂▃▄▅▆▇█'
    peak = max(values) if values and max(values) > 0 else 1
    return ''.join(bars[min(7, int(v / peak * 8))] for v in values)


def money(amount):
    return '%s %s' % (fmt_amount(int(round(amount * UNIT))), SYMBOL)


class Node:
    def __init__(self, chain, wallet, directory, miner, host, port, peers,
                 public_url='', admin_token='', max_reorg=MAX_REORG):
        self.chain = chain
        self.wallet = wallet
        self.directory = directory
        self.miner = miner
        self.host = host
        self.port = port
        self.public_url = public_url
        self.admin_token = admin_token
        self.max_reorg = max_reorg
        self.node_id = secrets.token_hex(8)
        self.lock = chain.lock
        self.guard = Guard()
        self.wake = threading.Event()
        self.pool = {}
        self.spent = {}
        self.dirty = False
        self.started = time.time()
        self.stats_cache = (0.0, None)
        self.peers = []
        self.peer_info = {}
        self.peer_meta = {}
        self.public_cache = {}
        self.warned_clock = set()
        self.history = deque(maxlen=120)
        self.peers_file = os.path.join(directory, 'peers.json')
        saved = []
        if os.path.exists(self.peers_file):
            try:
                with open(self.peers_file) as handle:
                    saved = json.load(handle)
            except (OSError, ValueError):
                saved = []
        if not isinstance(saved, list):
            saved = []
        for url in list(saved) + list(SEEDS) + list(peers):
            try:
                self.add_peer(url, save=False)
            except ValueError:
                pass

    def save_peers(self):
        manual = [u for u in self.peers if self.peer_meta.get(u, {}).get('manual')]
        temp = self.peers_file + '.tmp'
        with open(temp, 'w') as handle:
            json.dump(manual, handle)
        os.replace(temp, self.peers_file)

    def add_peer(self, url, save=True, manual=True):
        url = clean_url(url)
        parsed = urlparse(url)
        if url == self.public_url or (parsed.port == self.port and parsed.hostname in ('127.0.0.1', 'localhost', '0.0.0.0', '::1')):
            raise ValueError('itu alamat node ini sendiri')
        if not manual and not public_host(parsed.hostname):
            raise ValueError('alamat peer bukan alamat internet publik')
        with self.lock:
            if url not in self.peers:
                if len(self.peers) >= MAX_PEERS and not manual:
                    raise ValueError('daftar peer penuh')
                self.peers.append(url)
            meta = self.peer_meta.setdefault(url, {'fails': 0, 'bad_until': 0, 'manual': manual})
            if manual:
                meta['manual'] = True
                if save:
                    self.save_peers()
        return url

    def remove_peer(self, url):
        url = clean_url(url)
        with self.lock:
            if url in self.peers:
                self.peers.remove(url)
                self.peer_info.pop(url, None)
                self.peer_meta.pop(url, None)
                self.save_peers()

    def is_public(self, url):
        cached = self.public_cache.get(url)
        if cached and time.time() - cached[1] < 600:
            return cached[0]
        result = public_host(urlparse(url).hostname)
        self.public_cache[url] = (result, time.time())
        return result

    def usable_peers(self):
        now = time.time()
        return [u for u in list(self.peers) if self.peer_meta.get(u, {}).get('bad_until', 0) <= now]

    def broadcast(self, path, payload):
        for url in self.usable_peers():
            threading.Thread(target=self._post, args=(url + path, payload), daemon=True).start()

    @staticmethod
    def _post(url, payload):
        try:
            http_json(url, payload, timeout=5)
        except (OSError, ValueError):
            pass

    def announce(self):
        if not self.public_url:
            return
        for url in self.usable_peers():
            threading.Thread(target=self._post, args=(url + '/api/hello', {'url': self.public_url}),
                             daemon=True).start()

    def accept_hello(self, url):
        url = clean_url(url)
        if url in self.peers or url == self.public_url:
            return False
        if len(self.peers) >= MAX_PEERS:
            raise ValueError('daftar peer penuh')
        if not self.is_public(url):
            raise ValueError('alamat peer bukan alamat internet publik')
        try:
            info = http_json(url + '/api/status', timeout=5)
        except OSError:
            raise ValueError('peer tidak terjangkau')
        if info.get('name') != NAME or info.get('genesis') != GENESIS['hash']:
            raise ValueError('bukan node %s dengan genesis yang sama' % SYMBOL)
        if info.get('nodeId') == self.node_id:
            raise ValueError('itu node ini sendiri')
        self.add_peer(url, manual=False)
        log('PEER', 'peer baru: %s' % url, '35')
        self.wake.set()
        return True

    def gossip_list(self):
        urls = [u for u in self.peers if self.peer_info.get(u, {}).get('ok') and self.is_public(u)]
        if self.public_url:
            urls.append(self.public_url)
        return urls[:MAX_PEERS]

    def gossip(self):
        for url in self.usable_peers()[:4]:
            try:
                data = http_json(url + '/api/gossip')
                for item in list(data.get('peers', []))[:MAX_PEERS]:
                    if len(self.peers) >= MAX_PEERS:
                        return
                    try:
                        self.accept_hello(item)
                    except (OSError, ValueError):
                        pass
            except (OSError, ValueError, AttributeError, TypeError):
                pass

    def sync_loop(self):
        rounds = 0
        while True:
            self.wake.wait(SYNC_EVERY)
            self.wake.clear()
            rounds += 1
            try:
                if rounds % 5 == 1:
                    self.announce()
                for url in self.usable_peers():
                    self.sync_peer(url)
                if rounds % 5 == 2:
                    self.gossip()
            except Exception as error:
                log('PEER', 'kesalahan sinkronisasi: %s' % error, '31')
            time.sleep(1)

    def sync_peer(self, url):
        meta = self.peer_meta.setdefault(url, {'fails': 0, 'bad_until': 0, 'manual': False})
        try:
            if not meta['manual'] and not self.is_public(url):
                raise ValueError('bukan alamat internet publik')
            self.sync_with(url)
            meta['fails'] = 0
        except BadPeer as error:
            meta['bad_until'] = time.time() + BAN_SECONDS
            self.peer_info[url] = {'ok': False, 'height': None, 'seen': None,
                                   'error': ('data tidak sah: %s' % error)[:80]}
            log('PEER', '%s mengirim data tidak sah (%s); dilewati %d menit' % (url, error, BAN_SECONDS // 60), '31')
        except SelfPeer:
            log('PEER', '%s ternyata node ini sendiri, dihapus dari daftar' % url, '33')
            self.remove_peer(url)
        except (OSError, ValueError) as error:
            meta['fails'] += 1
            self.peer_info[url] = {'ok': False, 'height': None, 'seen': None, 'error': str(error)[:80]}
            if meta['fails'] >= 30 and not meta['manual']:
                self.remove_peer(url)

    def sync_with(self, url):
        info = http_json(url + '/api/status')
        if info.get('name') != NAME:
            raise ValueError('bukan node %s' % SYMBOL)
        if info.get('genesis', GENESIS['hash']) != GENESIS['hash']:
            raise ValueError('genesis berbeda (ini rantai lain)')
        if info.get('nodeId') == self.node_id:
            raise SelfPeer()
        height, work = info.get('height'), info.get('work')
        if (type(height) is not int or type(work) not in (int, float) or not math.isfinite(work)
                or height < 0 or height > 10 ** 9):
            raise BadPeer('status tidak valid')
        now = int(time.time() * 1000)
        self.peer_info[url] = {'ok': True, 'height': height, 'seen': now, 'error': None}
        remote_time = info.get('time')
        if type(remote_time) is int and abs(remote_time - now) > 60000 and url not in self.warned_clock:
            self.warned_clock.add(url)
            log('JAM', 'jam %s beda %d detik dari jam kamu; blok bisa ditolak. Aktifkan waktu otomatis di perangkat.'
                % (url, abs(remote_time - now) // 1000), '33')
        if work > self.chain.work + 1e-9 or height > self.chain.tip['index']:
            self.pull(url, height, work)
        pool = http_json(url + '/api/mempool?raw=1').get('txs', [])
        if isinstance(pool, list):
            for tx in pool[:MAX_MEMPOOL]:
                try:
                    self.add_tx(tx)
                except ValueError:
                    pass

    def pull(self, url, height, work):
        if height > self.chain.tip['index']:
            try:
                return self.pull_extend(url, height)
            except LookupError:
                pass
        self.reorg_from(url, height, work)

    def fetch_blocks(self, url, start):
        data = http_json('%s/api/blocks?from=%d&limit=%d' % (url, start, FETCH_BLOCKS))
        blocks = data.get('blocks', [])
        if not isinstance(blocks, list):
            raise BadPeer('daftar blok tidak valid')
        return blocks

    def pull_extend(self, url, target_height):
        while self.chain.tip['index'] < target_height:
            before = self.chain.tip['index']
            blocks = self.fetch_blocks(url, before + 1)
            if not blocks:
                return
            for block in blocks:
                try:
                    self.receive_block(block, strict=True)
                except ValueError as error:
                    if str(error) == 'invalid link':
                        raise LookupError('fork')
                    raise peer_error(error)
            if self.chain.tip['index'] == before:
                raise BadPeer('peer tidak memberi blok baru')

    def find_fork(self, url, peer_height):
        with self.lock:
            low, high = 0, min(self.chain.tip['index'], peer_height)
        while low < high:
            mid = (low + high + 1) // 2
            remote = http_json('%s/api/list?before=%d&limit=1' % (url, mid + 1)).get('blocks', [])
            with self.lock:
                own = self.chain.blocks[mid]['hash'] if mid < len(self.chain.blocks) else None
            if remote and remote[0].get('index') == mid and remote[0].get('hash') == own:
                low = mid
            else:
                high = mid - 1
        return low

    def reorg_from(self, url, height, claimed_work):
        fork = self.find_fork(url, height)
        with self.lock:
            own_tip = self.chain.tip['index']
            snapshot = list(self.chain.blocks[:fork + 1])
        if own_tip - fork > self.max_reorg:
            raise BadPeer('reorg terlalu dalam (%d blok, batas %d)' % (own_tip - fork, self.max_reorg))
        other = Chain.replay(snapshot)
        while other.tip['index'] < height:
            before = other.tip['index']
            blocks = self.fetch_blocks(url, before + 1)
            if not blocks:
                break
            for block in blocks:
                try:
                    other.add_block(block, persist=False)
                except ValueError as error:
                    raise peer_error(error)
            if other.tip['index'] == before:
                raise BadPeer('peer tidak memberi blok baru')
        if other.tip['index'] >= height and other.work < claimed_work - 1e-6:
            raise BadPeer('klaim work tidak terbukti')
        with self.lock:
            if other.work <= self.chain.work + 1e-9:
                return
            depth = self.chain.tip['index'] - fork
            if depth > self.max_reorg:
                raise BadPeer('reorg terlalu dalam (%d blok, batas %d)' % (depth, self.max_reorg))
            orphaned = [tx for b in self.chain.blocks[fork + 1:] for tx in b.get('txs', [])[1:]]
            self.chain.adopt(other)
            self.pool.clear()
            self.spent.clear()
            for tx in orphaned:
                try:
                    self.add_tx(tx, relay=False)
                except ValueError:
                    pass
            self.prune_pool()
            self.dirty = True
        log('SYNC', 'pindah ke rantai lebih berat dari %s (tinggi %d, %d blok diganti)' % (
            url, other.tip['index'], depth), '33')

    def add_tx(self, tx, relay=True):
        with self.lock:
            try:
                tx = clean_tx(tx)
                txid = tx['id']
                if txid in self.pool or txid in self.chain.tx_height:
                    return False
                size = len(json.dumps(tx))
                if size > MAX_TX_SIZE:
                    raise ValueError('transaksi terlalu besar')
                for item in tx['inputs']:
                    if (item['txid'], item['vout']) in self.spent:
                        raise ValueError('saldo ini sudah dipakai transaksi lain yang menunggu')
                fee = self.chain.check_tx(tx, set(), {}, len(self.chain.blocks))
            except (KeyError, TypeError, AttributeError, IndexError):
                raise ValueError('transaksi rusak')
            if fee < MIN_FEE:
                raise ValueError('biaya terlalu kecil (minimal %s %s)' % (fmt_amount(MIN_FEE), SYMBOL))
            if len(self.pool) >= MAX_MEMPOOL:
                worst = min(self.pool.values(), key=lambda e: e['fee'] / e['size'])
                if fee * worst['size'] <= worst['fee'] * size:
                    raise ValueError('mempool penuh')
                self.drop_tx(worst['tx']['id'])
            self.pool[txid] = {'tx': tx, 'fee': fee, 'size': size, 'time': int(time.time() * 1000)}
            for item in tx['inputs']:
                self.spent[(item['txid'], item['vout'])] = txid
            self.dirty = True
        log('TX', '%s... biaya %s %s' % (txid[:12], fmt_amount(fee), SYMBOL))
        if relay:
            self.broadcast('/api/tx', tx)
        return True

    def drop_tx(self, txid):
        entry = self.pool.pop(txid, None)
        if entry:
            for item in entry['tx']['inputs']:
                self.spent.pop((item['txid'], item['vout']), None)

    def prune_pool(self):
        with self.lock:
            for txid, entry in list(self.pool.items()):
                try:
                    ok = txid not in self.chain.tx_height
                    if ok:
                        self.chain.check_tx(entry['tx'], set(), {}, len(self.chain.blocks))
                except ValueError:
                    ok = False
                if not ok:
                    del self.pool[txid]
            self.spent = {(i['txid'], i['vout']): t for t, e in self.pool.items() for i in e['tx']['inputs']}

    def send(self, to, amount, fee):
        if not is_valid_address(to):
            raise ValueError('alamat tujuan tidak valid (harus JAB... dan mengandung 911)')
        if amount < DUST:
            raise ValueError('jumlah terlalu kecil')
        if fee < MIN_FEE:
            raise ValueError('biaya minimal %s %s' % (fmt_amount(MIN_FEE), SYMBOL))
        address = self.wallet['address']
        with self.lock:
            coins = [c for c in self.chain.spendable_utxos(address) if c[0] not in self.spent]
            coins.sort(key=lambda c: -c[1])
            available = sum(c[1] for c in coins)
            need = amount + fee
            chosen, total = [], 0
            for key, value in coins:
                chosen.append(key)
                total += value
                if total >= need:
                    break
            if total < need:
                raise ValueError('saldo yang bisa dikirim kurang (tersedia %s %s, butuh %s)' % (
                    fmt_amount(available), SYMBOL, fmt_amount(need)))
            outputs = [{'address': to, 'amount': amount}]
            change = total - need
            if change >= DUST:
                outputs.append({'address': address, 'amount': change})
            tx = {'inputs': [{'txid': k[0], 'vout': k[1]} for k in chosen], 'outputs': outputs}
            tx['id'] = tx_id(tx)
            signature = sign(self.wallet['privateKey'], tx['id'])
            for item in tx['inputs']:
                item['pubkey'] = self.wallet['publicKey']
                item['sig'] = signature
            self.add_tx(tx)
        return tx

    def template(self):
        with self.lock:
            chain = self.chain
            height = len(chain.blocks)
            ordered = sorted(self.pool.values(), key=lambda e: -e['fee'] / e['size'])
            spent, created, picked, fees = set(), {}, [], 0
            for entry in ordered:
                if len(picked) >= MAX_BLOCK_TXS:
                    break
                trial_spent, trial_created = set(spent), dict(created)
                try:
                    fee = chain.check_tx(entry['tx'], trial_spent, trial_created, height)
                except ValueError:
                    continue
                spent, created = trial_spent, trial_created
                picked.append(entry['tx'])
                fees += fee
            reward = chain.next_reward()
            coinbase = {'coinbase': height, 'inputs': [],
                        'outputs': [{'address': self.wallet['address'], 'amount': reward + fees}]}
            coinbase['id'] = tx_id(coinbase)
            txs = [coinbase] + picked
            block = {
                'index': height,
                'prevHash': chain.tip['hash'],
                'timestamp': max(int(time.time() * 1000), chain.tip['timestamp']),
                'difficulty': float(chain.next_difficulty()),
                'miner': self.wallet['address'],
                'reward': reward,
                'merkleRoot': merkle_root([t['id'] for t in txs]),
            }
            return block, txs

    def refresh_job(self):
        if not self.miner:
            return
        with self.lock:
            self.dirty = False
            block, txs = self.template()
            self.miner.set_job(block, txs)

    def housekeeping(self):
        if not self.miner:
            return
        with self.lock:
            current = self.miner.template[0] if self.miner.template else None
            if self.dirty or current is None or current['prevHash'] != self.chain.tip['hash']:
                self.refresh_job()

    def receive_block(self, block, strict=False):
        with self.lock:
            try:
                index = block['index']
                if type(index) is not int:
                    raise ValueError('malformed block')
                if index <= self.chain.tip['index']:
                    return False
                if index > self.chain.tip['index'] + 1 and not strict:
                    self.wake.set()
                    return False
            except (KeyError, TypeError):
                raise ValueError('malformed block')
            block = self.chain.add_block(block)
            self.prune_pool()
            self.dirty = True
        log('BLOK', 'dari jaringan #%d %s...' % (block['index'], block['hash'][:16]), '35')
        self.broadcast('/api/block', block)
        return True

    def collector(self):
        readers = list(self.miner.readers)
        while readers:
            for pipe in wait(readers, timeout=1):
                try:
                    job_id, nonce, digest = pipe.recv()
                except (EOFError, OSError):
                    readers.remove(pipe)
                    continue
                with self.lock:
                    if job_id != self.miner.job:
                        self.miner.stale += 1
                        continue
                    block, txs = self.miner.template
                    full = dict(block, txs=txs, nonce=nonce, hash=digest)
                    try:
                        self.chain.add_block(full)
                    except ValueError as error:
                        self.miner.rejected += 1
                        log('DITOLAK', str(error), '31')
                        self.refresh_job()
                        continue
                    self.miner.mined += 1
                    self.miner.last = int(time.time() * 1000)
                    self.prune_pool()
                    log('★ BLOK', '#%d %s...  +%s %s  (%d transfer)' % (
                        full['index'], full['hash'][:16], fmt_amount(txs[0]['outputs'][0]['amount']), SYMBOL,
                        len(txs) - 1), '1;32')
                    self.broadcast('/api/block', full)
                    self.refresh_job()

    def record_history(self):
        mine = sum(self.miner.rates) if self.miner else 0.0
        self.history.append([int(time.time() * 1000), mine, self.chain.network_hashrate(),
                             self.chain.tip['index']])

    def stats(self):
        cached = self.stats_cache
        if cached[1] is not None and time.time() - cached[0] < 1.5:
            return cached[1]
        data = self._stats()
        self.stats_cache = (time.time(), data)
        return data

    def _stats(self):
        data = self.chain.summary()
        address = self.wallet['address']
        with self.lock:
            balance = self.chain.balances.get(address, 0)
            spendable = sum(v for _, v in self.chain.spendable_utxos(address))
            pending = None
            if self.miner and self.miner.template:
                block, txs = self.miner.template
                tried = max(0, self.miner.total_hashes() - self.miner.job_base)
                pending = {'index': block['index'], 'transfers': len(txs) - 1,
                           'difficulty': block['difficulty'], 'reward': block['reward'] / UNIT,
                           'fees': (txs[0]['outputs'][0]['amount'] - block['reward']) / UNIT,
                           'prevHash': block['prevHash'], 'merkleRoot': block['merkleRoot'],
                           'target': target_for(block['difficulty']).hex(), 'timestamp': block['timestamp'],
                           'age': time.time() - self.miner.job_start, 'hashes': tried,
                           'luck': 1 - math.exp(-tried / (block['difficulty'] * HASHES_PER_DIFF))}
            data['mempool'] = {'count': len(self.pool), 'fees': sum(e['fee'] for e in self.pool.values()) / UNIT,
                               'bytes': sum(e['size'] for e in self.pool.values())}
            data['pending'] = pending
            data['node'] = {'mining': bool(self.miner), 'host': self.host, 'port': self.port,
                            'publicUrl': self.public_url or None, 'uptime': int(time.time() - self.started),
                            'nodeId': self.node_id, 'clock': int(time.time() * 1000),
                            'startedAt': int(self.started * 1000)}
            data['history'] = list(self.history)
            hashrate = sum(self.miner.rates) if self.miner else 0.0
            record = self.chain.mined.get(address, {})
            expected = data['difficulty'] * HASHES_PER_DIFF / hashrate if hashrate > 0 else None
            recent_found = [self.chain.brief(self.chain.blocks[h]) for h in reversed(record.get('heights', [])[-10:])]
            data['peers'] = [dict(self.peer_info.get(u, {'ok': None, 'height': None, 'seen': None, 'error': None}),
                                  url=u, manual=bool(self.peer_meta.get(u, {}).get('manual'))) for u in self.peers]
            data['miner'] = {
                'address': address,
                'balance': balance / UNIT,
                'spendable': spendable / UNIT,
                'immature': (balance - spendable) / UNIT,
                'hashrate': hashrate,
                'expectedSeconds': expected,
                'networkShare': min(100.0, hashrate / data['networkHashrate'] * 100) if data['networkHashrate'] > 0 else 0,
                'totalHashes': self.miner.total_hashes() if self.miner else 0,
                'threadHashes': list(self.miner.counters) if self.miner else [],
                'stale': self.miner.stale if self.miner else 0,
                'rejected': self.miner.rejected if self.miner else 0,
                'lifetimeBlocks': record.get('count', 0),
                'lifetimeReward': record.get('amount', 0) / UNIT,
                'recentBlocks': recent_found,
                'threads': list(self.miner.rates) if self.miner else [],
                'threadCount': self.miner.threads if self.miner else 0,
                'blocksMined': self.miner.mined if self.miner else 0,
                'lastBlockAt': self.miner.last if self.miner else None,
                'uptime': int(time.time() - self.started),
                'cpu': '%s x%d' % (platform.machine(), os.cpu_count() or 1),
            }
        return data

    def mempool_view(self):
        with self.lock:
            items = sorted(self.pool.values(), key=lambda e: -e['time'])
            result = []
            for entry in items:
                described = self.chain.describe(entry['tx'])
                described['size'] = entry['size']
                described['time'] = entry['time']
                result.append(described)
            return result


PROXY_HEADERS = ('Cf-Connecting-Ip', 'Cf-Ray', 'Cf-Visitor', 'Cdn-Loop', 'X-Forwarded-For', 'X-Forwarded-Host',
                 'X-Real-Ip', 'Forwarded', 'True-Client-Ip')
ADMIN_PATHS = ('/api/send', '/api/peers', '/api/peers/remove')
PUBLIC_POSTS = ('/api/tx', '/api/block', '/api/hello')
BENIGN = ('invalid link', 'too far ahead', 'penuh', 'biaya terlalu kecil', 'sudah dipakai', 'input not found',
          'coinbase not mature', 'double spend', 'terlalu besar')
CSP = ("default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'self'; "
       "img-src 'self' data:; base-uri 'none'; form-action 'none'; frame-ancestors 'none'")


class Server(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 64

    def __init__(self, *args, **kwargs):
        self.slots = threading.BoundedSemaphore(MAX_CONNECTIONS)
        super().__init__(*args, **kwargs)

    def process_request(self, request, client_address):
        if not self.slots.acquire(blocking=False):
            self.shutdown_request(request)
            return
        super().process_request(request, client_address)

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            self.slots.release()


class Handler(BaseHTTPRequestHandler):
    node = None
    timeout = 15
    server_version = 'JAB'
    sys_version = ''

    def log_message(self, *unused):
        pass

    def send_body(self, body, content_type, code=200):
        self.send_response(code)
        self.send_header('Content-Type', content_type)
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Referrer-Policy', 'no-referrer')
        if content_type.startswith('text/html'):
            self.send_header('Content-Security-Policy', CSP)
            self.send_header('X-Frame-Options', 'DENY')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, data, code=200):
        self.send_body(json.dumps(data).encode(), 'application/json', code)

    def via_proxy(self):
        return any(self.headers.get(name) for name in PROXY_HEADERS)

    def is_local(self):
        return self.client_address[0] in LOOPBACK and not self.via_proxy()

    def client_ip(self):
        address = self.client_address[0]
        if address in LOOPBACK:
            value = (self.headers.get('Cf-Connecting-Ip') or (self.headers.get('X-Forwarded-For') or '').split(',')[0]).strip()
            try:
                return str(ipaddress.ip_address(value))
            except ValueError:
                pass
        return address

    def is_admin(self):
        if not self.is_local():
            return False
        try:
            host = urlparse('//' + (self.headers.get('Host') or '')).hostname
        except ValueError:
            return False
        return host in ('127.0.0.1', 'localhost', '::1')

    def require_admin(self, ip):
        ok = self.is_admin()
        origin = self.headers.get('Origin')
        if ok and origin and urlparse(origin).netloc != self.headers.get('Host'):
            ok = False
        if ok:
            supplied = (self.headers.get('X-Admin-Token') or '').encode()
            ok = bool(self.node.admin_token) and hmac.compare_digest(supplied, self.node.admin_token.encode())
        if not ok:
            self.node.guard.strike(ip, 25)
            raise PermissionError('hanya bisa dari perangkat pemilik node (127.0.0.1) dengan token admin yang benar')

    def penalize(self, ip, path, error):
        if path in PUBLIC_POSTS and not self.is_local():
            if not any(word in str(error) for word in BENIGN):
                self.node.guard.strike(ip, 20 if path == '/api/hello' else 10)

    def do_GET(self):
        node = self.node
        url = urlparse(self.path)
        query = parse_qs(url.query)
        parts = [p for p in url.path.split('/') if p]
        try:
            if not self.is_local() and not node.guard.allow(self.client_ip(), 'read'):
                return self.send_json({'error': 'terlalu banyak permintaan, coba lagi nanti'}, 429)
            if not parts or parts == ['index.html']:
                token = node.admin_token if self.is_admin() else ''
                return self.send_body(HTML.replace('__ADMIN_TOKEN__', token).encode(), 'text/html; charset=utf-8')
            if parts == ['favicon.ico']:
                return self.send_body(b'', 'image/x-icon', 204)
            if parts[0] != 'api' or len(parts) < 2:
                raise LookupError
            self.send_json(self.route_get(parts[1:], query))
        except LookupError:
            self.send_json({'error': 'tidak ditemukan'}, 404)
        except ValueError as error:
            self.send_json({'error': str(error)}, 400)
        except Exception:
            self.send_json({'error': 'kesalahan server'}, 500)

    def route_get(self, parts, query):
        node, chain = self.node, self.node.chain
        name = parts[0]
        number = lambda key, default: int(query.get(key, [default])[0])
        if name == 'stats':
            return node.stats()
        if name == 'status':
            return {'name': NAME, 'version': VERSION, 'height': chain.tip['index'], 'tip': chain.tip['hash'],
                    'work': chain.work, 'genesis': GENESIS['hash'], 'nodeId': node.node_id,
                    'time': int(time.time() * 1000)}
        if name == 'blocks':
            start, limit = max(1, number('from', 1)), min(100, max(1, number('limit', 50)))
            with chain.lock:
                return {'blocks': chain.blocks[start:start + limit]}
        if name == 'list':
            with chain.lock:
                before = min(number('before', len(chain.blocks)), len(chain.blocks))
                limit = min(50, max(1, number('limit', 20)))
                items = [chain.brief(chain.blocks[i]) for i in range(before - 1, max(-1, before - 1 - limit), -1)]
                return {'blocks': items}
        if name == 'block' and len(parts) == 2:
            block = chain.get_block(parts[1])
            if block is None:
                raise LookupError
            return chain.block_detail(block)
        if name == 'tx' and len(parts) == 2:
            with node.lock:
                found = chain.get_tx(parts[1])
                if found:
                    data = chain.describe(found[0], found[1])
                    data['status'] = 'confirmed'
                    return data
                if parts[1] in node.pool:
                    data = chain.describe(node.pool[parts[1]]['tx'])
                    data['status'] = 'pending'
                    return data
            raise LookupError
        if name == 'address' and len(parts) == 2:
            return chain.address_info(parts[1])
        if name == 'mempool':
            if query.get('raw'):
                with node.lock:
                    return {'txs': [e['tx'] for e in node.pool.values()]}
            return {'txs': node.mempool_view()}
        if name == 'chart':
            return {'blocks': chain.chart(min(200, max(10, number('limit', 60))))}
        if name == 'peers':
            return {'peers': node.stats()['peers']}
        if name == 'gossip':
            return {'peers': node.gossip_list()}
        raise LookupError

    def do_POST(self):
        node = self.node
        ip = self.client_ip()
        path = urlparse(self.path).path
        try:
            local = self.is_local()
            if not local and node.guard.is_banned(ip):
                return self.send_json({'error': 'diblokir sementara karena terlalu banyak permintaan tidak sah'}, 403)
            bucket = {'/api/tx': 'tx', '/api/block': 'block', '/api/hello': 'hello'}.get(path, 'admin')
            if not local and not node.guard.allow(ip, bucket):
                return self.send_json({'error': 'terlalu banyak permintaan, coba lagi nanti'}, 429)
            if (self.headers.get('Content-Type') or '').split(';')[0].strip().lower() != 'application/json':
                return self.send_json({'error': 'Content-Type harus application/json'}, 415)
            length = int(self.headers.get('Content-Length') or 0)
            if length < 0 or length > MAX_BODY.get(path, 8192):
                return self.send_json({'error': 'ukuran data tidak diizinkan'}, 413)
            body = json.loads(self.rfile.read(length) or b'{}')
            if not isinstance(body, dict):
                raise ValueError('isi permintaan harus objek JSON')
            if path in ADMIN_PATHS:
                self.require_admin(ip)
            if path == '/api/send':
                tx = node.send(str(body.get('to', '')).strip(), parse_amount(body.get('amount')),
                               parse_amount(body.get('fee', fmt_amount(MIN_FEE * 10))))
                return self.send_json({'id': tx['id']})
            if path == '/api/tx':
                return self.send_json({'accepted': node.add_tx(body)})
            if path == '/api/block':
                return self.send_json({'accepted': node.receive_block(body)})
            if path == '/api/hello':
                return self.send_json({'accepted': node.accept_hello(body.get('url', ''))})
            if path == '/api/peers':
                return self.send_json({'url': node.add_peer(body.get('url', ''))})
            if path == '/api/peers/remove':
                node.remove_peer(body.get('url', ''))
                return self.send_json({'ok': True})
            self.send_json({'error': 'tidak ditemukan'}, 404)
        except PermissionError as error:
            self.send_json({'error': str(error)}, 403)
        except ValueError as error:
            self.penalize(ip, path, error)
            self.send_json({'error': str(error)}, 400)
        except Exception:
            self.send_json({'error': 'kesalahan server'}, 500)


USAGE = """%(name)s v%(version)s
Blockchain proof-of-work dengan penambang bawaan, dashboard web, dan jaringan peer-to-peer.

Pemakaian:
  python %(script)s [PERINTAH] [OPSI]

Perintah:
  run                      jalankan node + penambang + dashboard (default bila kosong)
  status                   tampilkan status lengkap node yang sedang jalan
  peers                    daftar peer dan kondisinya
  wallet [--show-key]      tampilkan alamat dompet (dan private key)
  balance [ALAMAT]         lihat saldo dari data di disk
  send TUJUAN JUMLAH       kirim JAB lewat node yang sedang jalan
  addpeer URL              tambah peer ke node yang sedang jalan
  newwallet                buat alamat baru (disimpan sendiri oleh kamu)
  version                  tampilkan versi
  help                     tampilkan bantuan ini

Opsi penambangan:
  --threads N       jumlah proses penambang (default: setengah core)
  --no-mine         hanya jadi node, tidak menambang

Opsi jaringan:
  --port N          port dashboard (default 8911)
  --host IP         default 127.0.0.1; 0.0.0.0 agar bisa diakses dari jaringan lokal
  --peers URL,URL   node lain, contoh https://node.contoh.com atau http://192.168.1.5:8911
  --public-url URL  alamat publik node ini (mis. URL Cloudflare Tunnel), diumumkan ke peer
  --max-reorg N     batas kedalaman reorg dalam blok (default %(reorg)d)

Opsi data:
  --data FOLDER     folder data (default jab_data)
  --reverify        cek ulang semua tanda tangan saat memuat blok dari disk

Opsi tampilan:
  --status DETIK    jeda cetak panel status saat jalan (default %(every)d, 0 = mati)
  --compact         status satu baris, cocok untuk log panjang
  --no-color        matikan warna (otomatis mati bila NO_COLOR diset atau output bukan terminal)

Opsi transaksi:
  --fee JUMLAH      biaya untuk perintah send (default 0.0001)

Contoh:
  python %(script)s
  python %(script)s --threads 4 --port 8912
  python %(script)s --no-mine --peers http://192.168.1.5:8911
  python %(script)s --status 30 --compact
  python %(script)s send JAB... 1.5 --fee 0.0002
  python %(script)s status --port 8912

Aturan rantai:
  Suplai maksimum %(supply)s %(symbol)s, hadiah awal %(reward)s %(symbol)s, halving tiap %(halving)s blok
  Target waktu blok %(target)d dtk, kesulitan disesuaikan tiap %(adjust)d blok
  Hadiah blok matang setelah %(maturity)d blok, biaya minimum %(minfee)s %(symbol)s
"""

BOOLEAN_FLAGS = {'--no-mine', '--show-key', '--help', '--reverify', '--compact', '--no-color', '--version'}


def show_help():
    text = USAGE % {
        'name': NAME, 'version': VERSION, 'reorg': MAX_REORG, 'every': STATUS_EVERY,
        'script': os.path.basename(__file__), 'symbol': SYMBOL,
        'supply': format(MAX_SUPPLY // UNIT, ','), 'reward': fmt_amount(INITIAL_REWARD),
        'halving': format(HALVING, ','), 'target': TARGET_TIME, 'adjust': ADJUST,
        'maturity': COINBASE_MATURITY, 'minfee': fmt_amount(MIN_FEE),
    }
    out, current = [], ''
    for line in text.split('\n'):
        if line and not line[0].isspace():
            current = line
            out.append(color(line, '1;33') if line.endswith(':') else color(line, '1;37'))
            continue
        if current in ('Perintah:', 'Opsi penambangan:', 'Opsi jaringan:', 'Opsi data:', 'Opsi tampilan:', 'Opsi transaksi:'):
            line = re.sub(r'^(  )(\S.*?\S|\S)(\s{2,})(\S.*)$',
                          lambda m: m.group(1) + color(m.group(2), '36') + m.group(3) + m.group(4), line)
        elif current == 'Contoh:':
            line = re.sub(r'^(  )(python)', lambda m: m.group(1) + dim('$') + ' ' + m.group(2), line)
        out.append(line)
    print('\n'.join(out))


def option(args, name, default):
    flag = '--' + name
    if flag in args and args.index(flag) + 1 < len(args):
        return args[args.index(flag) + 1]
    return default


def positional(args):
    items, skip = [], False
    for token in args:
        if skip:
            skip = False
        elif token.startswith('--'):
            skip = token not in BOOLEAN_FLAGS
        else:
            items.append(token)
    return items


def format_rate(value):
    units = ['H/s', 'KH/s', 'MH/s', 'GH/s', 'TH/s']
    i = 0
    while value >= 1000 and i < len(units) - 1:
        value /= 1000
        i += 1
    return '%.2f %s' % (value, units[i])


def format_duration(seconds):
    if seconds is None:
        return '-'
    if seconds < 60:
        return '%d dtk' % seconds
    if seconds < 3600:
        return '%.1f mnt' % (seconds / 60)
    if seconds < 86400:
        return '%.1f jam' % (seconds / 3600)
    return '%.1f hari' % (seconds / 86400)


def write_private(path, text):
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, 'w') as handle:
        handle.write(text)


def secure_dir(directory):
    os.makedirs(directory, exist_ok=True)
    try:
        os.chmod(directory, 0o700)
    except OSError:
        pass


def load_wallet(directory):
    secure_dir(directory)
    path = os.path.join(directory, 'wallet.json')
    if os.path.exists(path):
        try:
            if os.stat(path).st_mode & 0o077:
                os.chmod(path, 0o600)
        except OSError:
            pass
        with open(path) as handle:
            wallet = json.load(handle)
        if address_of(wallet.get('publicKey', '')) != wallet.get('address'):
            sys.exit('wallet.json rusak: alamat tidak cocok dengan public key.')
        return wallet
    wallet = create_wallet()
    write_private(path, json.dumps(wallet, indent=2))
    return wallet


def load_admin_token(directory):
    secure_dir(directory)
    path = os.path.join(directory, 'admin_token')
    if not os.path.exists(path):
        write_private(path, secrets.token_hex(32))
    with open(path) as handle:
        return handle.read().strip()


def in_blocks(count):
    return 'di blok berikutnya' if count <= 0 else '%d blok lagi' % count


def since(ms):
    return 'belum ada' if not ms else '%s lalu' % format_duration(max(0, time.time() - ms / 1000))


def print_status(full, compact=False):
    m = full['miner']
    mining = full['node']['mining']
    peers = full['peers']
    live = sum(1 for p in peers if p.get('ok'))
    if compact:
        work = '⛏ %s' % format_rate(m['hashrate']) if mining else 'node saja'
        print(' │ '.join([dim(clock()), color('#%d' % full['height'], '1;37'), work,
                          'kesulitan %.3f' % full['difficulty'], 'saldo %s' % money(m['balance']),
                          'peer %d/%d' % (live, len(peers)), 'mempool %d' % full['mempool']['count'],
                          'ditambang %d' % m['blocksMined']]), flush=True)
        return
    state = color('⛏  MENAMBANG', '1;32') if mining else color('●  NODE SAJA', '1;36')
    average = full['averageBlockTime']
    lines = ['', heading(color('◆ %s' % NAME, '1;33'), '%s  %s' % (state, dim(clock()))),
             section('RANTAI'),
             kv('Blok', '%s   kesulitan %.3f   hadiah %s' % (color('#%d' % full['height'], '1;37'), full['difficulty'], money(full['reward']))),
             kv('Waktu blok', '%s dtk rata-rata, target %d dtk' % ('%.1f' % average if average else '-', full['targetBlockTime'])),
             kv('Berikutnya', 'kesulitan disesuaikan %s, halving %s' % (in_blocks(full['blocksUntilAdjust']), in_blocks(full['blocksUntilHalving'])))]
    if mining:
        pending = full['pending']
        expected = m['expectedSeconds']
        lines += [section('PENAMBANG'),
                  kv('Hashrate', '%s%s%s%s%.3f%%' % (color(format_rate(m['hashrate']), '1;33'), dim('   jaringan '),
                                                   format_rate(full['networkHashrate']), dim('   pangsa '), m['networkShare'])),
                  kv('Thread', '%s  %d proses' % (color(spark(m['threads']), '33'), len(m['threads'])))]
        if pending:
            lines += [kv('Menggali', 'blok #%d, %d transfer, umur %s' % (pending['index'], pending['transfers'], format_duration(pending['age']))),
                      kv('Peluang', '%s %.1f%%' % (gauge(pending['luck']), pending['luck'] * 100))]
        lines += [kv('Estimasi', 'blok per %s%s' % (format_duration(expected), ', sekitar %.2f blok/hari' % (86400 / expected) if expected else '')),
                  kv('Sesi', '%d blok ditemukan, %d ditolak, %d basi' % (m['blocksMined'], m['rejected'], m['stale'])),
                  kv('Total hash', format(int(m['totalHashes']), ',')),
                  kv('Blok terakhir', since(m['lastBlockAt']))]
    lines += [section('DOMPET'),
              kv('Saldo', color(money(m['balance']), '1;32')),
              kv('Bisa kirim', money(m['spendable'])),
              kv('Matang', 'menunggu %s' % money(m['immature'])),
              kv('Seumur hidup', '%d blok, hadiah %s' % (m['lifetimeBlocks'], money(m['lifetimeReward']))),
              section('JARINGAN'),
              kv('Peer', '%d terhubung dari %d' % (live, len(peers))),
              kv('Mempool', '%d transaksi, biaya %s' % (full['mempool']['count'], money(full['mempool']['fees']))),
              kv('Rantai', '%d transfer, %d pemegang, %d penambang' % (full['totalTransfers'], full['holders'], full['minerCount'])),
              section('SUPLAI'),
              kv('Beredar', '%s %.4f%%' % (gauge(full['supplyPercent'] / 100, 28), full['supplyPercent'])),
              kv('Dari', '%s %s, era hadiah ke-%d' % (format(int(full['maxSupply']), ','), SYMBOL, full['era']))]
    print('\n'.join(lines), flush=True)


def print_peers(full):
    peers = full['peers']
    live = sum(1 for p in peers if p.get('ok'))
    lines = ['', heading(color('◆ Peer', '1;33'), dim('%d terhubung dari %d' % (live, len(peers)))), '']
    if not peers:
        lines.append('    ' + dim('belum ada peer. Tambahkan dengan: addpeer URL'))
    for p in peers:
        if p.get('ok'):
            diff = (p.get('height') or 0) - full['height']
            note = 'tinggi %s (%s)' % (p.get('height'), 'sama' if diff == 0 else '%+d' % diff)
            mark = color('●', '32')
        elif p.get('ok') is None:
            note, mark = 'belum dicek', color('●', '33')
        else:
            note, mark = p.get('error') or 'tidak terjangkau', color('●', '31')
        lines.append('    %s %s  %s' % (mark, p['url'], dim(note)))
    print('\n'.join(lines), flush=True)


def print_banner(node, wallet, directory, mine, threads, host, port, public_url):
    mode = color('⛏  menambang dengan %d proses' % threads, '32') if mine else color('●  node saja (tanpa menambang)', '36')
    lines = ['', heading(color('◆ %s' % NAME, '1;33'), dim('v%s' % VERSION)), '',
             kv('Alamat', color(wallet['address'], '1;37')),
             kv('Dashboard', color('http://127.0.0.1:%d' % port, '4;36')),
             kv('Mode', mode),
             kv('Tinggi', '#%d' % node.chain.tip['index']),
             kv('Data', directory),
             kv('Peer', ', '.join(node.peers) or '-'),
             kv('Publik', public_url or dim('- (tambahkan --public-url agar peer lain bisa menghubungi balik)')),
             kv('Admin', 'token di %s' % os.path.join(directory, 'admin_token')),
             kv('', dim('jangan dibagikan; kirim dana hanya dari 127.0.0.1'))]
    if host not in ('127.0.0.1', 'localhost', '::1'):
        lines.append(kv('Peringatan', color('dashboard terbuka untuk jaringan; kirim dana tetap hanya bisa dari 127.0.0.1.', '33')))
    lines += ['', '  ' + dim('Ctrl+C untuk berhenti. Atur status dengan --status DETIK atau --compact. Bantuan: --help'), '']
    print('\n'.join(lines), flush=True)


def print_summary(node):
    try:
        full = node.stats()
    except Exception:
        print('\nBerhenti...')
        return
    m = full['miner']
    lines = ['', heading(color('◆ Sesi selesai', '1;33'), dim(clock())), '',
             kv('Aktif', format_duration(full['node']['uptime'])),
             kv('Tinggi', '#%d' % full['height'])]
    if full['node']['mining']:
        lines += [kv('Ditemukan', '%d blok, %d ditolak, %d basi' % (m['blocksMined'], m['rejected'], m['stale'])),
                  kv('Total hash', format(int(m['totalHashes']), ','))]
    lines += [kv('Saldo', color(money(m['balance']), '1;32')), '', '  ' + dim('Berhenti...'), '']
    print('\n'.join(lines), flush=True)


def run_node(args):
    try:
        mp.set_start_method('fork')
    except (RuntimeError, ValueError):
        pass
    mine = '--no-mine' not in args
    threads = max(1, int(option(args, 'threads', max(1, (os.cpu_count() or 2) // 2))))
    port = int(option(args, 'port', 8911))
    host = option(args, 'host', '127.0.0.1')
    directory = os.path.abspath(option(args, 'data', 'jab_data'))
    peers = [p for p in option(args, 'peers', '').split(',') if p.strip()]
    max_reorg = int(option(args, 'max-reorg', MAX_REORG))
    status_every = max(0, int(option(args, 'status', STATUS_EVERY)))
    compact = '--compact' in args
    public_url = option(args, 'public-url', '').strip()
    if public_url:
        if not re.match(r'^https?://', public_url):
            sys.exit('--public-url harus diawali http:// atau https:// (contoh: https://nama.trycloudflare.com)')
        try:
            public_url = clean_url(public_url)
        except ValueError as error:
            sys.exit('--public-url tidak valid: %s' % error)
    wallet = load_wallet(directory)
    token = load_admin_token(directory)
    chain = Chain(directory, reverify='--reverify' in args)
    miner = Miner(threads) if mine else None
    node = Node(chain, wallet, directory, miner, host, port, peers, public_url, token, max_reorg)
    Handler.node = node
    try:
        server = Server((host, port), Handler)
    except OSError as error:
        sys.exit('Port %d tidak bisa dipakai (%s). Coba: --port %d' % (port, error, port + 1))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    threading.Thread(target=node.sync_loop, daemon=True).start()
    if miner:
        threading.Thread(target=node.collector, daemon=True).start()

    print_banner(node, wallet, directory, mine, threads, host, port, public_url)
    node.refresh_job()
    tick = 0
    try:
        while True:
            time.sleep(1)
            tick += 1
            node.housekeeping()
            if miner and tick % 5 == 0:
                miner.sample()
            if tick % 5 == 0:
                node.record_history()
            if status_every and tick % status_every == 0:
                print_status(node.stats(), compact)
    except KeyboardInterrupt:
        print_summary(node)
        server.shutdown()
        sys.exit(0)


def admin_headers(directory):
    path = os.path.join(directory, 'admin_token')
    if not os.path.exists(path):
        sys.exit('Token admin tidak ada di %s. Jalankan node sekali dulu dari folder yang sama.' % directory)
    with open(path) as handle:
        return {'X-Admin-Token': handle.read().strip()}


def main():
    args = sys.argv[1:]
    if '--no-color' in args:
        STYLE['on'] = False
    if '--help' in args or '-h' in args or (args and args[0] == 'help'):
        show_help()
        return
    if '--version' in args or (args and args[0] == 'version'):
        print('%s v%s' % (NAME, VERSION))
        return
    command = args[0] if args and not args[0].startswith('--') else 'run'
    rest = positional(args[1:] if args and not args[0].startswith('--') else args)
    directory = os.path.abspath(option(args, 'data', 'jab_data'))
    port = int(option(args, 'port', 8911))
    if command == 'run':
        run_node(args)
    elif command == 'wallet':
        wallet = load_wallet(directory)
        print(heading(color('◆ Dompet', '1;33')))
        print(kv('Alamat', color(wallet['address'], '1;37')))
        print(kv('Saldo', color('%s %s' % (fmt_amount(int(Chain(directory).balances.get(wallet['address'], 0))), SYMBOL), '1;32')))
        if '--show-key' in args:
            print(kv('Private key', color(wallet['privateKey'], '1;31')))
            print('    ' + dim('Simpan baik-baik. Siapa pun yang punya key ini bisa memakai koinmu.'))
        else:
            print('    ' + dim('Tambahkan --show-key untuk menampilkan private key.'))
    elif command == 'balance':
        address = rest[0] if rest else load_wallet(directory)['address']
        info = Chain(directory).address_info(address)
        print(heading(color('◆ Saldo', '1;33')))
        print(kv('Alamat', color(address, '1;37')))
        print(kv('Saldo', color('%s %s' % (info['balance'], SYMBOL), '1;32')))
        print(kv('Bisa kirim', '%s %s' % (info['spendable'], SYMBOL)))
        print(kv('Matang', 'menunggu %s %s' % (info['immature'], SYMBOL)))
    elif command == 'send':
        if len(rest) < 2:
            sys.exit('Pemakaian: send TUJUAN JUMLAH [--fee 0.0001]')
        try:
            result = http_json('http://127.0.0.1:%d/api/send' % port,
                               {'to': rest[0], 'amount': rest[1], 'fee': option(args, 'fee', '0.0001')},
                               headers=admin_headers(directory))
        except ValueError as error:
            sys.exit('Gagal: %s' % error)
        except OSError:
            sys.exit('Node belum jalan di port %d. Jalankan dulu: python %s' % (port, os.path.basename(__file__)))
        print(heading(color('✓ Terkirim', '1;32')))
        print(kv('Tujuan', rest[0]))
        print(kv('Jumlah', '%s %s' % (rest[1], SYMBOL)))
        print(kv('Biaya', '%s %s' % (option(args, 'fee', '0.0001'), SYMBOL)))
        print(kv('ID transaksi', color(result['id'], '1;37')))
    elif command == 'addpeer':
        if not rest:
            sys.exit('Pemakaian: addpeer URL')
        try:
            result = http_json('http://127.0.0.1:%d/api/peers' % port, {'url': rest[0]},
                               headers=admin_headers(directory))
        except ValueError as error:
            sys.exit('Gagal: %s' % error)
        except OSError:
            sys.exit('Node belum jalan di port %d.' % port)
        print('%s %s' % (color('✓ Peer ditambahkan', '1;32'), result['url']))
    elif command == 'newwallet':
        wallet = create_wallet()
        print(json.dumps(wallet, indent=2))
        print(color('Simpan privateKey dengan aman. Alamat ini bisa dipakai sebagai tujuan send.', '33'))
    elif command == 'status':
        try:
            full = http_json('http://127.0.0.1:%d/api/stats' % port)
        except (ValueError, OSError):
            sys.exit('Node belum jalan di port %d. Jalankan dulu: python %s' % (port, os.path.basename(__file__)))
        print_status(full, '--compact' in args)
    elif command == 'peers':
        try:
            full = http_json('http://127.0.0.1:%d/api/stats' % port)
        except (ValueError, OSError):
            sys.exit('Node belum jalan di port %d. Jalankan dulu: python %s' % (port, os.path.basename(__file__)))
        print_peers(full)
    else:
        sys.exit('Perintah tidak dikenal: %s\nCoba: --help' % command)
HTML = r"""<!DOCTYPE html>
<html lang="id">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#061418">
<title>Jilatan Ambatukam</title>
<style>
:root{
  --bg:#061418;--surface:#0f262d;--glass:rgba(20,48,57,.62);--line:#25474f;--text:#eaf3ef;--mute:#8fa9a8;
  --gold:#f0bf55;--gold-grad:linear-gradient(135deg,#ffe08f 0%,#f0bf55 45%,#d99320 100%);--on-gold:#1a1304;
  --ok:#58d6a5;--bad:#ff8272;--blue:#6cb8ff;--glow:rgba(240,191,85,.16);--grid:rgba(255,255,255,.025);
  --shadow:0 16px 40px -16px rgba(0,0,0,.6);
  --serif:"Iowan Old Style","Palatino Linotype",Palatino,"Noto Serif",Georgia,serif;
  --sans:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
}
@media (prefers-color-scheme:light){:root{
  --bg:#eaf1ed;--surface:#ffffff;--glass:rgba(255,255,255,.78);--line:#c3d5ce;--text:#10282e;--mute:#566f6d;
  --gold:#9a6700;--gold-grad:linear-gradient(135deg,#d9a21f 0%,#b97a05 55%,#8f5c00 100%);--on-gold:#ffffff;
  --ok:#0f7a56;--bad:#b3372b;--blue:#1b6fb8;--glow:rgba(185,122,5,.14);--grid:rgba(16,40,46,.04);
  --shadow:0 16px 36px -18px rgba(16,40,46,.35);
}}
*{box-sizing:border-box;margin:0;padding:0}
html{-webkit-text-size-adjust:100%;scroll-behavior:smooth}
body{background:var(--bg);color:var(--text);font:15px/1.55 var(--sans);-webkit-font-smoothing:antialiased;
  padding:max(18px,env(safe-area-inset-top)) 16px calc(120px + env(safe-area-inset-bottom));min-height:100vh}
body::before{content:"";position:fixed;inset:0;z-index:-1;pointer-events:none;
  background:
    radial-gradient(60% 38% at 88% -6%,var(--glow),transparent 70%),
    radial-gradient(48% 36% at -4% 34%,color-mix(in srgb,var(--blue) 11%,transparent),transparent 70%),
    radial-gradient(50% 34% at 104% 100%,color-mix(in srgb,var(--ok) 9%,transparent),transparent 70%),
    linear-gradient(var(--grid) 1px,transparent 1px) 0 0/44px 44px,
    linear-gradient(90deg,var(--grid) 1px,transparent 1px) 0 0/44px 44px}
.wrap{max-width:800px;margin:0 auto}
a{color:inherit}
::selection{background:var(--gold);color:var(--on-gold)}
:focus-visible{outline:2px solid var(--gold);outline-offset:3px;border-radius:8px}
[hidden]{display:none!important}

.top{display:flex;align-items:center;gap:14px;padding:4px 0 22px}
.logo{width:46px;height:46px;flex:none;filter:drop-shadow(0 8px 14px var(--glow))}
.top>div:nth-child(2){flex:1;min-width:0}
.brand{font:700 21px/1.05 var(--serif);letter-spacing:-.01em}
.tag{color:var(--mute);font-size:12px;line-height:1.4;margin-top:5px;max-width:34ch}
.pill{display:inline-flex;align-items:center;gap:8px;border:1px solid var(--line);border-radius:999px;
  padding:7px 13px;font-size:12.5px;font-weight:600;white-space:nowrap;
  background:color-mix(in srgb,var(--surface) 80%,transparent);backdrop-filter:blur(12px);-webkit-backdrop-filter:blur(12px)}
.dot{width:9px;height:9px;border-radius:50%;background:var(--bad)}
.dot.on{background:var(--ok);animation:ring 2s ease-out infinite}
@keyframes ring{0%{box-shadow:0 0 0 0 color-mix(in srgb,var(--ok) 55%,transparent)}100%{box-shadow:0 0 0 9px transparent}}

.view{animation:rise .45s cubic-bezier(.2,.7,.2,1) both}
@keyframes rise{from{opacity:0;transform:translateY(12px)}to{opacity:1;transform:none}}

h2{display:flex;align-items:center;gap:10px;font:700 11.5px/1.2 var(--sans);letter-spacing:.16em;text-transform:uppercase;
  color:var(--mute);margin:36px 0 12px}
h2::before{content:"";width:20px;height:3px;border-radius:3px;background:var(--gold-grad)}
h2 small{font:500 12px var(--sans);letter-spacing:0;text-transform:none;color:var(--mute);margin-left:auto}
.view>h2:first-child,#bdetail>h2:first-child{font:800 28px/1.15 var(--sans);letter-spacing:-.025em;text-transform:none;color:var(--text);margin-bottom:14px}
.view>h2:first-child::before,#bdetail>h2:first-child::before{display:none}

.plate{position:relative;overflow:hidden;border-radius:28px;padding:24px 22px 16px;box-shadow:var(--shadow);
  background:linear-gradient(155deg,color-mix(in srgb,var(--gold) 15%,var(--surface)) 0%,var(--surface) 58%);
  border:1px solid color-mix(in srgb,var(--gold) 30%,var(--line))}
.plate::before{content:"";position:absolute;right:-70px;top:-80px;width:240px;height:240px;border-radius:50%;
  background:radial-gradient(circle,var(--glow),transparent 68%);pointer-events:none}
.plate::after{content:"";position:absolute;left:0;right:0;top:0;height:1px;
  background:linear-gradient(90deg,transparent,color-mix(in srgb,var(--gold) 70%,transparent),transparent)}
.plate>*{position:relative}
.plate .lead{color:var(--mute);font-size:12px;font-weight:600;letter-spacing:.08em;text-transform:uppercase;display:flex;align-items:center;gap:10px}
.big{font:800 clamp(34px,10.5vw,54px)/1.05 var(--sans);letter-spacing:-.035em;word-break:break-all;margin-top:8px;font-variant-numeric:tabular-nums}
.big b{background:var(--gold-grad);-webkit-background-clip:text;background-clip:text;color:transparent;-webkit-text-fill-color:transparent}
.big span{font:700 16px var(--sans);letter-spacing:.06em;color:var(--mute);margin-left:10px;-webkit-text-fill-color:var(--mute)}
.sub{color:var(--mute);font-size:13px;margin-top:6px}
.addr{display:block;width:100%;text-align:left;cursor:pointer;color:var(--mute);font:12px/1.5 var(--mono);word-break:break-all;
  padding:11px 14px;margin:14px 0 8px;min-height:44px;border-radius:14px;
  background:color-mix(in srgb,var(--bg) 45%,transparent);border:1px solid var(--line);transition:border-color .2s,transform .15s}
.addr:hover{border-color:var(--gold)}
.addr:active{transform:scale(.99)}
.addr b{display:inline-block;color:var(--gold);font:700 11px var(--sans);letter-spacing:.06em;text-transform:uppercase;margin-left:8px;
  padding:2px 9px;border-radius:999px;background:color-mix(in srgb,var(--gold) 14%,transparent)}

.led{display:flex;align-items:baseline;gap:10px;padding:7px 0}
.led .k{color:var(--mute);font-size:14px}
.led .d{flex:1;border-bottom:1.5px dotted color-mix(in srgb,var(--line) 85%,transparent);transform:translateY(-4px);min-width:12px}
.led .v{text-align:right;font-weight:600;font-variant-numeric:tabular-nums;overflow-wrap:anywhere}
.led .v.mono{font:12px var(--mono);font-weight:500}

.panel{background:var(--glass);border:1px solid var(--line);border-radius:22px;padding:8px 18px;box-shadow:var(--shadow)}
.panel:empty{display:none}
.panel .empty{border:0;margin:0;padding:18px 0}
.panel>.item:last-child,.panel>.tx:last-child{border-bottom:0}
.panel .led:last-child{border-bottom:0}

.cards{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-top:14px}
@media (min-width:640px){.cards{grid-template-columns:repeat(4,1fr)}}
.card{position:relative;overflow:hidden;background:var(--glass);border:1px solid var(--line);border-radius:20px;padding:15px 16px;min-width:0;
  transition:transform .2s,border-color .2s}
.card:hover{transform:translateY(-2px);border-color:color-mix(in srgb,var(--gold) 45%,var(--line))}
.card small{display:block;color:var(--mute);font-size:11px;font-weight:600;letter-spacing:.07em;text-transform:uppercase}
.card b{display:block;font:800 21px/1.2 var(--sans);letter-spacing:-.02em;font-variant-numeric:tabular-nums;overflow-wrap:anywhere;margin-top:5px}
.card.gold{border-color:color-mix(in srgb,var(--gold) 38%,var(--line));
  background:linear-gradient(150deg,color-mix(in srgb,var(--gold) 18%,transparent),var(--glass))}
.card.gold b{background:var(--gold-grad);-webkit-background-clip:text;background-clip:text;color:transparent;-webkit-text-fill-color:transparent}

.rail{display:flex;gap:16px;overflow-x:auto;padding:8px 4px 18px;scroll-snap-type:x proximity;scrollbar-width:thin;scrollbar-color:var(--line) transparent}
.link{position:relative;flex:0 0 auto;width:150px;border:1.5px solid var(--line);border-radius:20px;
  padding:13px 14px;text-decoration:none;background:var(--glass);scroll-snap-align:end;
  display:flex;flex-direction:column;gap:3px;transition:transform .2s,border-color .2s,box-shadow .2s}
a.link:hover{transform:translateY(-4px);border-color:var(--gold);box-shadow:0 14px 26px -14px var(--glow)}
.link:not(:last-child)::after{content:"";position:absolute;left:100%;top:50%;width:16px;height:3px;margin-top:-1.5px;border-radius:2px;background:var(--line)}
.link b{font:800 21px var(--sans);letter-spacing:-.02em;color:var(--gold)}
.link span{font-size:12px;color:var(--mute)}
.link .hash{font-family:var(--mono);color:var(--text);opacity:.85}
.link.pending{border:1.5px dashed var(--gold);
  background-image:linear-gradient(100deg,transparent 30%,color-mix(in srgb,var(--gold) 22%,transparent) 50%,transparent 70%);
  background-size:250% 100%;animation:sweep 2.4s linear infinite}
.link.pending.idle{animation:none;border-color:var(--line)}
.link.pending.idle b{color:var(--mute)}
.link:has(+ .pending)::after{background:repeating-linear-gradient(90deg,var(--gold) 0 4px,transparent 4px 8px)}
@keyframes sweep{from{background-position:150% 0}to{background-position:-100% 0}}
@keyframes beat{0%,100%{box-shadow:0 0 0 0 color-mix(in srgb,var(--gold) 55%,transparent)}50%{box-shadow:0 0 0 10px transparent}}
@media (prefers-reduced-motion:reduce){
  .link.pending,.pulse.on,.dot.on,.view{animation:none}
  html{scroll-behavior:auto}
}

.pulse{width:12px;height:12px;border-radius:50%;background:var(--mute);display:inline-block;flex:none}
.pulse.on{background:var(--gold);animation:beat 1.3s ease-in-out infinite}

.bar{height:10px;border-radius:999px;background:color-mix(in srgb,var(--line) 75%,transparent);overflow:hidden;margin:10px 0 8px}
.bar i{display:block;height:100%;background:var(--gold-grad);border-radius:999px;box-shadow:0 0 14px var(--glow);transition:width .6s cubic-bezier(.2,.7,.2,1)}
.bar.blue i{background:var(--blue)}
.thread{display:grid;grid-template-columns:34px 1fr 86px 60px;gap:10px;align-items:center;font-size:12px;margin:9px 0}
.thread .bar{margin:0;height:8px}.thread b{text-align:right;font-weight:700;font-variant-numeric:tabular-nums}
.thread em{font-style:normal;color:var(--mute);text-align:right;font-variant-numeric:tabular-nums}
svg.chart{width:100%;height:160px;display:block;margin-top:6px;padding:12px 10px;border-radius:20px;
  background:var(--glass);border:1px solid var(--line);overflow:visible}
.legend{display:flex;gap:18px;flex-wrap:wrap;font-size:12px;color:var(--mute);margin-top:10px;padding:0 4px}
.legend i{display:inline-block;width:16px;height:4px;margin-right:7px;vertical-align:middle;border-radius:3px}

.item{display:flex;justify-content:space-between;align-items:center;gap:12px;padding:13px 0;
  border-bottom:1px solid color-mix(in srgb,var(--line) 70%,transparent);text-decoration:none;min-height:56px;transition:color .2s}
.item:hover .t{color:var(--gold)}
.item .l{min-width:0}.item .t{font-weight:700;transition:color .2s}
.item .s{font:12px/1.4 var(--mono);color:var(--mute);overflow-wrap:anywhere}
.item .r{text-align:right;font-weight:600;font-variant-numeric:tabular-nums;white-space:nowrap}
.pos{color:var(--ok)}.neg{color:var(--bad)}.mute{color:var(--mute)}
.item .r .mute{font-weight:400;font-size:12px}
.empty{color:var(--mute);padding:20px;text-align:center;border:1px dashed var(--line);border-radius:18px;margin:10px 0}
.tagchip{display:inline-block;font-size:10.5px;font-weight:600;letter-spacing:.05em;text-transform:uppercase;
  border:1px solid var(--line);border-radius:999px;padding:1px 9px;margin-left:8px;color:var(--mute);vertical-align:middle}

label{display:block;font-weight:600;font-size:13px;color:var(--mute);margin:18px 0 7px}
input{width:100%;font:16px var(--sans);padding:13px 15px;border:1px solid var(--line);border-radius:14px;
  background:color-mix(in srgb,var(--bg) 50%,var(--surface));color:var(--text);transition:border-color .2s,box-shadow .2s}
input::placeholder{color:color-mix(in srgb,var(--mute) 75%,transparent)}
input:focus{outline:0;border-color:var(--gold);box-shadow:0 0 0 4px var(--glow)}
.row2{display:grid;grid-template-columns:1fr 1fr;gap:12px}
#sendform{background:var(--glass);border:1px solid var(--line);border-radius:24px;padding:2px 20px 22px;margin-top:16px;box-shadow:var(--shadow)}
#sendform .btn{width:100%}
.btn{font:700 15px var(--sans);letter-spacing:.01em;min-height:50px;padding:0 24px;border-radius:14px;border:0;
  background:var(--gold-grad);color:var(--on-gold);cursor:pointer;margin-top:20px;
  box-shadow:0 10px 22px -10px color-mix(in srgb,var(--gold) 80%,transparent),inset 0 1px 0 rgba(255,255,255,.4);
  transition:transform .15s,filter .15s,box-shadow .2s}
.btn:hover{filter:brightness(1.08)}
.btn:active{transform:scale(.97)}
.btn.ghost{background:var(--glass);color:var(--text);border:1px solid var(--line);margin-top:0;box-shadow:none}
.btn.ghost:hover{border-color:var(--gold);filter:none}
.btn[disabled]{opacity:.55;pointer-events:none}
.search{display:flex;gap:10px;margin-top:4px}.search input{flex:1}.search .btn{margin-top:0}
.note{margin-top:14px;padding:13px 16px;border-radius:14px;border:1px solid var(--line);font-size:14px;overflow-wrap:anywhere;
  background:color-mix(in srgb,var(--surface) 70%,transparent)}
.note.err{border-color:var(--bad);color:var(--bad);background:color-mix(in srgb,var(--bad) 9%,transparent)}
.note.ok{border-color:var(--ok);background:color-mix(in srgb,var(--ok) 9%,transparent)}
.note a{color:var(--gold);font-weight:700}
.hint{color:var(--mute);font-size:13px;margin-top:10px;line-height:1.5}

.tx{background:var(--glass);border:1px solid var(--line);border-radius:20px;padding:15px 16px;margin-bottom:12px}
.tx .t{margin-bottom:2px}
.tx .id{display:block;font:12px var(--mono);color:var(--mute);overflow-wrap:anywhere;text-decoration:none;transition:color .2s}
.tx .id:hover{color:var(--gold)}
.flow{display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-top:12px;padding-top:12px;font-size:13px;
  border-top:1px dashed color-mix(in srgb,var(--line) 90%,transparent)}
.flow div{min-width:0}.flow small{display:block;color:var(--mute);font-size:11px;font-weight:600;letter-spacing:.07em;text-transform:uppercase;margin-bottom:4px}
.flow a{font:12px/1.5 var(--mono);overflow-wrap:anywhere;display:block;transition:color .2s}
.flow a:hover{color:var(--gold)}
#bdetail>.led{padding:9px 0}

nav{position:fixed;left:0;right:0;bottom:0;z-index:5;padding:0 14px calc(12px + env(safe-area-inset-bottom));pointer-events:none}
nav div{pointer-events:auto;max-width:540px;margin:0 auto;display:grid;grid-template-columns:repeat(5,1fr);gap:2px;padding:6px;
  border-radius:26px;border:1px solid var(--line);
  background:color-mix(in srgb,var(--surface) 82%,transparent);
  backdrop-filter:blur(20px) saturate(150%);-webkit-backdrop-filter:blur(20px) saturate(150%);
  box-shadow:0 18px 44px -12px rgba(0,0,0,.55)}
nav a{display:flex;flex-direction:column;align-items:center;gap:4px;padding:9px 2px 8px;border-radius:20px;text-decoration:none;
  font-weight:600;font-size:11px;letter-spacing:.01em;color:var(--mute);transition:color .2s,background .2s,transform .15s}
nav a:active{transform:scale(.94)}
nav a svg{width:22px;height:22px;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
nav a:hover{color:var(--text)}
nav a[aria-current=page]{color:var(--gold);background:color-mix(in srgb,var(--gold) 14%,transparent);
  box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--gold) 30%,transparent)}

@media (max-width:380px){
  .brand{font-size:18px}
  .row2{grid-template-columns:1fr}
  .flow{grid-template-columns:1fr}
  nav a{font-size:10px}
}
</style>
</head>
<body>
<div class="wrap">
<header class="top">
  <svg class="logo" viewBox="0 0 40 40" aria-hidden="true"><defs><linearGradient id="lg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#ffe08f"/><stop offset="1" stop-color="#d99320"/></linearGradient></defs><rect width="40" height="40" rx="13" fill="url(#lg)"/><path d="M20 9l9 5v11l-9 5-9-5V14z" fill="none" stroke="#1a1304" stroke-width="2.4" stroke-linejoin="round"/><path d="M11 14l9 5 9-5M20 19v11" fill="none" stroke="#1a1304" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"/></svg>
  <div>
    <div class="brand">Jilatan<br>Ambatukam</div>
    <div class="tag">Blockchain proof-of-work, maksimal 30 juta JAB <span id="ver"></span></div>
  </div>
  <div class="pill" role="status"><span class="dot" id="dot"></span><span id="status">Menyambung</span></div>
</header>

<section class="view" id="v-ringkasan">
  <div class="plate">
    <div class="lead">Saldo dompet ini</div>
    <div class="big"><b id="bal" style="font-weight:700">0</b><span>JAB</span></div>
    <button class="addr" id="addr" type="button" aria-label="Salin alamat dompet">-</button>
    <div id="walletrows"></div>
  </div>

  <h2>Rantai terbaru</h2>
  <div class="rail" id="rail" tabindex="0" aria-label="Blok terbaru"></div>

  <div class="cards" id="topcards"></div>

  <h2>Statistik rantai</h2>
  <div class="panel" id="chainrows"></div>

  <h2>Jaringan</h2>
  <div class="panel" id="netrows"></div>

  <h2>Pasokan</h2>
  <div class="bar"><i id="supbar" style="width:0%"></i></div>
  <div class="panel" id="suprows"></div>

  <h2>Waktu antar blok <small>60 blok terakhir</small></h2>
  <svg class="chart" id="c-time" viewBox="0 0 600 140" preserveAspectRatio="none" role="img" aria-label="Grafik waktu antar blok"></svg>
  <div class="legend"><span><i style="background:var(--gold)"></i>Selang blok (dtk)</span><span><i style="background:var(--mute)"></i>Target</span></div>

  <h2>Kesulitan <small>60 blok terakhir</small></h2>
  <svg class="chart" id="c-diff" viewBox="0 0 600 140" preserveAspectRatio="none" role="img" aria-label="Grafik kesulitan"></svg>
  <div class="legend"><span id="diffnote"></span></div>

  <h2>Hashrate <small>10 menit terakhir</small></h2>
  <svg class="chart" id="c-hash" viewBox="0 0 600 140" preserveAspectRatio="none" role="img" aria-label="Grafik hashrate"></svg>
  <div class="legend"><span><i style="background:var(--gold)"></i>Hashrate kamu</span><span><i style="background:var(--mute)"></i>Jaringan</span></div>

  <h2>Pemegang terbesar</h2>
  <div class="panel" id="top"></div>
</section>

<section class="view" id="v-blok" hidden>
  <form class="search" id="searchform" role="search">
    <input id="q" type="search" placeholder="Nomor blok, hash, ID transaksi, atau alamat" aria-label="Cari">
    <button class="btn" type="submit">Cari</button>
  </form>
  <div id="searchnote" class="note err" hidden></div>
  <div id="blist">
    <div class="cards" id="blockcards"></div>
    <h2>Semua blok</h2>
    <div class="panel" id="blocks"></div>
    <button class="btn ghost" id="more" type="button" style="margin-top:14px">Muat blok lebih lama</button>
  </div>
  <div id="bdetail" hidden></div>
</section>

<section class="view" id="v-tambang" hidden>
  <div class="plate">
    <div class="lead"><span class="pulse" id="mpulse"></span><span id="mstate">-</span></div>
    <div class="big"><b id="mrate" style="font-weight:700">0 H/s</b></div>
    <div class="sub" id="mshare"></div>
  </div>

  <div id="minebox">
    <h2>Blok yang sedang digali</h2>
    <div class="panel" id="jobrows"></div>
    <div class="bar"><i id="luckbar" style="width:0%"></i></div>
    <div class="hint" id="lucknote"></div>

    <h2>Estimasi</h2>
    <div class="panel" id="estrows"></div>

    <h2>Sesi ini</h2>
    <div class="panel" id="sessrows"></div>

    <h2>Tenaga penambang</h2>
    <div class="panel" id="threads"></div>
  </div>

  <h2>Riwayat hashrate <small>10 menit terakhir</small></h2>
  <svg class="chart" id="c-hash2" viewBox="0 0 600 140" preserveAspectRatio="none" role="img" aria-label="Grafik hashrate penambang"></svg>
  <div class="legend"><span><i style="background:var(--gold)"></i>Hashrate kamu</span><span><i style="background:var(--mute)"></i>Jaringan</span></div>

  <h2>Seluruh waktu</h2>
  <div class="panel" id="lifetime"></div>

  <h2>Blok yang kamu temukan <small>10 terbaru</small></h2>
  <div class="panel" id="found"></div>
</section>

<section class="view" id="v-kirim" hidden>
  <h2 style="margin-top:6px">Kirim JAB</h2>
  <div class="led"><span class="k">Bisa dikirim sekarang</span><i class="d"></i><span class="v" id="spend">-</span></div>
  <div class="led"><span class="k">Menunggu matang</span><i class="d"></i><span class="v" id="immature">-</span></div>
  <form id="sendform" autocomplete="off">
    <label for="to">Alamat tujuan</label>
    <input id="to" name="to" placeholder="JAB..." autocapitalize="off" spellcheck="false" required>
    <div class="row2">
      <div><label for="amount">Jumlah</label><input id="amount" name="amount" inputmode="decimal" placeholder="0.0" required></div>
      <div><label for="fee">Biaya</label><input id="fee" name="fee" inputmode="decimal" value="0.0001" required></div>
    </div>
    <p class="hint">Biaya diberikan ke penambang yang memasukkan transaksimu ke blok. Hadiah blok baru bisa dikirim setelah 5 blok.</p>
    <button class="btn" id="sendbtn" type="submit">Kirim JAB</button>
  </form>
  <div id="sendnote" class="note" hidden></div>
</section>

<section class="view" id="v-jaringan" hidden>
  <h2 style="margin-top:6px">Node ini</h2>
  <div class="panel" id="noderows"></div>

  <h2>Identitas rantai</h2>
  <div class="panel" id="idrows"></div>

  <h2>Aturan konsensus</h2>
  <div class="panel" id="rulerows"></div>

  <h2>Peer <small id="peercount"></small></h2>
  <div class="panel" id="peers"></div>
  <form class="search" id="peerform" style="margin-top:12px">
    <input id="peerurl" placeholder="http://192.168.1.5:8911" inputmode="url" autocapitalize="off" aria-label="Alamat peer">
    <button class="btn" type="submit">Tambah</button>
  </form>
  <div id="peernote" class="note" hidden></div>

  <h2>Mempool</h2>
  <div class="panel" id="poolrows"></div>
  <h2>Transaksi menunggu <small id="poolcount"></small></h2>
  <div id="pool"></div>
</section>
</div>

<nav aria-label="Menu utama"><div>
  <a href="#/ringkasan" data-tab="ringkasan"><svg viewBox="0 0 24 24" aria-hidden="true"><rect x="3" y="3" width="7" height="9" rx="2"/><rect x="14" y="3" width="7" height="5" rx="2"/><rect x="14" y="12" width="7" height="9" rx="2"/><rect x="3" y="16" width="7" height="5" rx="2"/></svg>Ringkasan</a>
  <a href="#/blok" data-tab="blok"><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 3l8 4.5v9L12 21l-8-4.5v-9z"/><path d="M4 7.5l8 4.5 8-4.5M12 12v9"/></svg>Blok</a>
  <a href="#/tambang" data-tab="tambang"><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M13 2L4 14h7l-1 8 9-12h-7z"/></svg>Tambang</a>
  <a href="#/kirim" data-tab="kirim"><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M21 3L10 14"/><path d="M21 3l-7 18-4-7-7-4z"/></svg>Kirim</a>
  <a href="#/jaringan" data-tab="jaringan"><svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="5" r="2.5"/><circle cx="5" cy="18" r="2.5"/><circle cx="19" cy="18" r="2.5"/><path d="M10.5 7.2L6.3 15.8M13.5 7.2l4.2 8.6M7.5 18h9"/></svg>Jaringan</a>
</div></nav>

<script>
const ADMIN_TOKEN = "__ADMIN_TOKEN__";
const HPD = 65536;
const $ = (id) => document.getElementById(id);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const num = (v, d = 4) => Number(v).toLocaleString('id-ID', { maximumFractionDigits: d });
const short = (s, a = 8, b = 6) => !s ? '-' : (s.length > a + b + 3 ? s.slice(0, a) + '...' + s.slice(-b) : s);
const scale = (v, units) => {
  let i = 0;
  while (v >= 1000 && i < units.length - 1) { v /= 1000; i++; }
  return v.toFixed(i === 0 && units[0] === '' ? 0 : 2) + ' ' + units[i];
};
const rate = (v) => scale(v, ['H/s', 'KH/s', 'MH/s', 'GH/s', 'TH/s']);
const count = (v) => scale(v, ['', 'K', 'M', 'G', 'T', 'P']).trim();
const bytes = (n) => {
  const u = ['B', 'KB', 'MB', 'GB'];
  let i = 0;
  while (n >= 1024 && i < u.length - 1) { n /= 1024; i++; }
  return (i ? n.toFixed(2) : Math.round(n)) + ' ' + u[i];
};
const span = (s) => {
  if (s === null || s === undefined || !isFinite(s)) return '-';
  if (s < 60) return Math.round(s) + ' dtk';
  if (s < 3600) return (s / 60).toFixed(1) + ' mnt';
  if (s < 86400) return (s / 3600).toFixed(1) + ' jam';
  if (s < 86400 * 365) return (s / 86400).toFixed(1) + ' hari';
  return (s / 86400 / 365).toFixed(1) + ' tahun';
};
const dur = (s) => `${Math.floor(s / 3600)} j ${Math.floor((s % 3600) / 60)} m ${s % 60} d`;
const ago = (t) => {
  if (!t) return 'belum ada';
  const s = Math.max(0, Math.floor((Date.now() - t) / 1000));
  if (s < 60) return s + ' dtk lalu';
  if (s < 3600) return Math.floor(s / 60) + ' mnt lalu';
  if (s < 86400) return Math.floor(s / 3600) + ' jam lalu';
  return Math.floor(s / 86400) + ' hari lalu';
};
const when = (t) => t ? new Date(t).toLocaleString('id-ID', { dateStyle: 'medium', timeStyle: 'medium' }) : '-';
const led = (k, v, mono) => `<div class="led"><span class="k">${k}</span><i class="d"></i><span class="v${mono ? ' mono' : ''}">${v}</span></div>`;
const rows = (id, list) => { $(id).innerHTML = list.map((r) => led(r[0], r[1], r[2])).join(''); };
const cards = (id, list) => { $(id).innerHTML = list.map((c) => `<div class="card${c[2] ? ' gold' : ''}"><small>${c[0]}</small><b>${c[1]}</b></div>`).join(''); };
const jab = (v, d = 8) => num(v, d) + ' JAB';
const pct = (v, d = 2) => num(v, d) + '%';
const aLink = (a) => a ? `<a href="#/alamat/${esc(a)}">${esc(short(a, 10, 8))}</a>` : '-';

async function api(path, body) {
  const headers = { 'Content-Type': 'application/json' };
  if (ADMIN_TOKEN) headers['X-Admin-Token'] = ADMIN_TOKEN;
  const options = body === undefined ? { cache: 'no-store' }
    : { method: 'POST', headers, body: JSON.stringify(body) };
  const response = await fetch(path, options);
  const data = await response.json().catch(() => ({ error: 'Respon server tidak valid' }));
  if (!response.ok) throw new Error(data.error || 'Error ' + response.status);
  return data;
}

async function copyText(text) {
  try { await navigator.clipboard.writeText(text); return true; } catch (e) {}
  const area = document.createElement('textarea');
  area.value = text; document.body.appendChild(area); area.select();
  let ok = false;
  try { ok = document.execCommand('copy'); } catch (e) {}
  area.remove();
  return ok;
}

let stats = null, railHeight = -1, listHeight = -1, listBefore = 0, listMode = false, chartHeight = -1;

function plot(id, series) {
  const el = $(id);
  const all = series.flatMap((s) => s.data.filter((v) => v !== null && v !== undefined));
  if (!all.length) { el.innerHTML = ''; return; }
  const max = Math.max(1e-9, ...all);
  const grid = [35, 70, 105].map((y) => `<line x1="0" x2="600" y1="${y}" y2="${y}" stroke="var(--line)" stroke-width="1" stroke-opacity=".6" vector-effect="non-scaling-stroke"/>`).join('');
  const body = series.map((s, k) => {
    const n = s.data.length;
    if (n < 2) return '';
    const pts = s.data.map((v, i) => `${(i / (n - 1)) * 600},${135 - ((v || 0) / max) * 125}`).join(' ');
    const fill = s.dash ? '' :
      `<defs><linearGradient id="${id}-g${k}" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="${s.color}" stop-opacity=".38"/><stop offset="1" stop-color="${s.color}" stop-opacity="0"/></linearGradient></defs>` +
      `<polygon points="0,135 ${pts} 600,135" fill="url(#${id}-g${k})"/>`;
    return fill + `<polyline points="${pts}" fill="none" stroke="${s.color}" stroke-width="${s.width || 2.5}" stroke-linejoin="round" stroke-linecap="round"${s.dash ? ' stroke-dasharray="5 4"' : ''} vector-effect="non-scaling-stroke"/>`;
  }).join('');
  el.innerHTML = grid + body;
}

function renderRail(s) {
  const rail = $('rail');
  const blocks = s.recent.slice().reverse();
  const pend = s.pending;
  const html = blocks.map((b) =>
    `<a class="link" href="#/blok/${b.index}"><b>#${b.index}</b><span class="hash">${esc(short(b.hash, 6, 4))}</span>` +
    `<span>${b.transfers ? b.transfers + ' transfer' : 'hanya hadiah'}</span><span>${ago(b.timestamp)}</span></a>`).join('');
  const next = pend
    ? `<div class="link pending${s.node.mining ? '' : ' idle'}"><b>#${pend.index}</b><span>${s.node.mining ? 'mencari nonce' : 'menunggu'}</span><span>${pend.transfers} transfer</span></div>`
    : `<div class="link pending idle"><b>#${s.height + 1}</b><span>blok berikutnya</span><span>node tanpa mining</span></div>`;
  rail.innerHTML = html + next;
  if (railHeight !== s.height) { rail.scrollLeft = rail.scrollWidth; railHeight = s.height; }
}

function renderMining(s) {
  const m = s.miner, p = s.pending, on = s.node.mining;
  $('mpulse').classList.toggle('on', on);
  $('mstate').textContent = on ? 'Menambang dengan ' + m.threadCount + ' proses' : 'Mode node saja (tanpa menambang)';
  $('mrate').textContent = rate(m.hashrate);
  $('mshare').textContent = on ? 'Pangsa jaringan ' + pct(m.networkShare, 3) + ' dari ' + rate(s.networkHashrate) : 'Jalankan tanpa --no-mine untuk menambang.';
  $('minebox').hidden = !on;
  if (on) {
    const claim = p ? p.reward + p.fees : 0;
    rows('jobrows', [
      ['Blok target', p ? '#' + num(p.index, 0) : '-'],
      ['Kesulitan', p ? num(p.difficulty, 3) : '-'],
      ['Target hash', p ? esc(short(p.target, 10, 6)) : '-', true],
      ['Hadiah blok', p ? jab(p.reward) : '-'],
      ['Biaya transaksi di blok', p ? jab(p.fees) : '-'],
      ['Total yang diklaim', p ? jab(claim) : '-'],
      ['Transfer di blok', p ? num(p.transfers, 0) : '-'],
      ['Hash sebelumnya', p ? esc(short(p.prevHash, 10, 6)) : '-', true],
      ['Merkle root', p ? esc(short(p.merkleRoot, 10, 6)) : '-', true],
      ['Umur pekerjaan', p ? span(p.age) : '-'],
      ['Hash dicoba di pekerjaan ini', p ? count(p.hashes) : '-'],
    ]);
    const luck = p ? p.luck * 100 : 0;
    $('luckbar').style.width = Math.max(0.5, luck) + '%';
    $('lucknote').textContent = p ? 'Peluang secara statistik sudah menemukan blok ini: ' + luck.toFixed(1) + '%' : '';
    const exp = m.expectedSeconds;
    rows('estrows', [
      ['Peluang tiap hash', exp ? '1 banding ' + count(s.difficulty * HPD) : '-'],
      ['Rata-rata waktu menemukan blok', span(exp)],
      ['Perkiraan blok per hari', exp ? num(86400 / exp, 2) : '-'],
      ['Perkiraan hadiah per hari', exp ? jab((86400 / exp) * s.reward, 4) : '-'],
      ['Pangsa jaringan', pct(m.networkShare, 3)],
    ]);
    rows('sessrows', [
      ['Blok ditemukan sesi ini', num(m.blocksMined, 0)],
      ['Blok ditolak / basi', num(m.rejected, 0) + ' / ' + num(m.stale, 0)],
      ['Total hash dicoba', count(m.totalHashes)],
      ['Blok terakhir ditemukan', ago(m.lastBlockAt)],
      ['Aktif sejak', dur(m.uptime)],
    ]);
    const peak = Math.max(1, ...m.threads);
    $('threads').innerHTML = m.threads.map((r, i) =>
      `<div class="thread"><span>T${i}</span><div class="bar"><i style="width:${(r / peak) * 100}%"></i></div><b>${rate(r)}</b><em>${count(m.threadHashes[i] || 0)}</em></div>`).join('');
  }
  rows('lifetime', [
    ['Total blok ditambang', num(m.lifetimeBlocks, 0)],
    ['Total hadiah diterima', jab(m.lifetimeReward)],
    ['Saldo dompet', jab(m.balance)],
    ['Bisa dikirim', jab(m.spendable)],
    ['Menunggu matang', jab(m.immature)],
  ]);
  const maturity = s.rules.maturity;
  $('found').innerHTML = m.recentBlocks.length ? m.recentBlocks.map((b) => {
    const left = maturity - (s.height + 1 - b.index);
    return `<a class="item" href="#/blok/${b.index}"><div class="l"><div class="t">Blok ${b.index}</div><div class="s">${esc(short(b.hash, 12, 8))}</div></div>` +
      `<div class="r pos">+${jab(b.reward + b.fees)}<div class="mute">${left > 0 ? 'matang ' + left + ' blok lagi' : 'sudah matang'}</div></div></a>`;
  }).join('') : '<div class="empty">Belum ada blok yang ditemukan dompet ini.</div>';
  plot('c-hash2', [
    { data: s.history.map((h) => h[2]), color: 'var(--mute)', width: 2, dash: true },
    { data: s.history.map((h) => h[1]), color: 'var(--gold)' },
  ]);
}

function render(s) {
  stats = s;
  const m = s.miner;
  $('ver').textContent = 'v' + s.version;
  $('bal').textContent = num(m.balance, 8);
  $('addr').innerHTML = esc(m.address) + '<b>salin</b>';
  $('addr').dataset.addr = m.address;
  rows('walletrows', [
    ['Bisa dikirim', jab(m.spendable)],
    ['Menunggu matang', jab(m.immature)],
    ['Blok yang kamu temukan', num(m.lifetimeBlocks, 0)],
    ['Blok terakhir', ago(m.lastBlockAt)],
  ]);
  renderRail(s);
  cards('topcards', [
    ['Tinggi blok', num(s.height, 0), true],
    ['Kesulitan', num(s.difficulty, 3)],
    ['Hashrate jaringan', rate(s.networkHashrate)],
    ['Hadiah blok', jab(s.reward, 4)],
  ]);
  rows('chainrows', [
    ['Tinggi blok', num(s.height, 0)],
    ['Total transfer', num(s.totalTransfers, 0)],
    ['Total biaya dibayar', jab(s.totalFees)],
    ['Pemegang koin', num(s.holders, 0)],
    ['Alamat pernah aktif', num(s.addresses, 0)],
    ['Saldo belum terpakai (UTXO)', num(s.utxoCount, 0)],
    ['Penambang unik', num(s.minerCount, 0)],
    ['Ukuran data rantai', bytes(s.dataSize)],
    ['Blok terakhir', ago(s.recent[0] && s.recent[0].timestamp)],
  ]);
  rows('netrows', [
    ['Hashrate jaringan', rate(s.networkHashrate)],
    ['Hashrate kamu', rate(m.hashrate)],
    ['Kesulitan', num(s.difficulty, 3)],
    ['Waktu blok rata-rata', (s.averageBlockTime ? s.averageBlockTime.toFixed(1) : '-') + ' dtk dari target ' + s.targetBlockTime + ' dtk'],
    ['Total kerja (work)', num(s.totalWork, 2)],
    ['Perkiraan total hash', count(s.totalHashes)],
    ['Penyesuaian kesulitan', s.blocksUntilAdjust === 0 ? 'di blok berikutnya' : num(s.blocksUntilAdjust, 0) + ' blok lagi'],
    ['Halving berikutnya', 'blok ' + num(s.nextHalvingHeight, 0) + ', ' + num(s.blocksUntilHalving, 0) + ' blok lagi'],
    ['Transaksi menunggu', num(s.mempool.count, 0)],
  ]);
  $('supbar').style.width = Math.max(0.3, Math.min(100, s.supplyPercent)) + '%';
  rows('suprows', [
    ['Beredar', jab(s.circulatingSupply)],
    ['Maksimum', jab(s.maxSupply, 0)],
    ['Tersisa', jab(s.remainingSupply)],
    ['Sudah ditambang', s.supplyPercent.toFixed(6) + '%'],
    ['Era hadiah', 'ke-' + s.era + ', halving berikutnya menjadi ' + jab(s.nextHalvingReward, 4)],
  ]);
  plot('c-hash', [
    { data: s.history.map((h) => h[2]), color: 'var(--mute)', width: 2, dash: true },
    { data: s.history.map((h) => h[1]), color: 'var(--gold)' },
  ]);
  $('top').innerHTML = s.topHolders.length ? s.topHolders.map((h, i) =>
    `<a class="item" href="#/alamat/${esc(h.address)}"><div class="l"><div class="t">Peringkat ${i + 1}</div><div class="s">${esc(short(h.address, 12, 8))}</div></div><div class="r">${jab(h.balance)}<div class="mute">${pct(h.share, 2)} dari suplai</div></div></a>`).join('')
    : '<div class="empty">Belum ada koin beredar. Biarkan penambang berjalan sampai blok pertama ditemukan.</div>';

  cards('blockcards', [
    ['Tinggi', num(s.height, 0), true],
    ['Total transfer', num(s.totalTransfers, 0)],
    ['Waktu blok rata-rata', s.averageBlockTime ? s.averageBlockTime.toFixed(1) + ' dtk' : '-'],
    ['Total biaya', jab(s.totalFees, 4)],
  ]);

  $('spend').textContent = jab(m.spendable);
  $('immature').textContent = jab(m.immature);
  $('dot').classList.add('on');
  $('status').textContent = s.node.mining ? 'Menambang' : 'Node aktif';

  renderMining(s);

  const drift = Math.abs(s.node.clock - Date.now());
  rows('noderows', [
    ['Versi', esc(s.version)],
    ['Mode', s.node.mining ? 'Menambang dengan ' + m.threadCount + ' proses' : 'Node saja'],
    ['Host dan port', esc(s.node.host) + ':' + s.node.port],
    ['Alamat publik', s.node.publicUrl ? esc(s.node.publicUrl) : 'belum diatur'],
    ['ID node', esc(s.node.nodeId), true],
    ['Aktif sejak', when(s.node.startedAt) + ' (' + dur(s.node.uptime) + ')'],
    ['CPU', esc(m.cpu)],
    ['Ukuran data rantai', bytes(s.dataSize)],
    ['Selisih jam dengan peramban', Math.round(drift / 1000) + ' dtk'],
  ]);
  rows('idrows', [
    ['Tinggi', num(s.height, 0)],
    ['Hash ujung rantai', esc(s.tip), true],
    ['Hash genesis', esc(s.genesis), true],
    ['Total kerja (work)', num(s.totalWork, 2)],
    ['Perkiraan total hash', count(s.totalHashes)],
  ]);
  const r = s.rules;
  rows('rulerows', [
    ['Target waktu blok', r.targetBlockTime + ' dtk'],
    ['Penyesuaian kesulitan', 'tiap ' + r.adjustEvery + ' blok'],
    ['Halving', 'tiap ' + num(r.halving, 0) + ' blok'],
    ['Hadiah awal', jab(r.initialReward, 4)],
    ['Biaya minimum', jab(r.minFee)],
    ['Output terkecil', jab(r.dust)],
    ['Kematangan hadiah blok', r.maturity + ' blok'],
    ['Transfer maksimum per blok', num(r.maxBlockTxs, 0)],
    ['Kapasitas mempool', num(r.maxMempool, 0) + ' transaksi'],
    ['Kedalaman reorg maksimum', r.maxReorg + ' blok'],
  ]);
  const live = s.peers.filter((p) => p.ok).length;
  $('peercount').textContent = live + ' terhubung dari ' + s.peers.length;
  $('peers').innerHTML = s.peers.length ? s.peers.map((p) => {
    const diff = p.height !== null && p.height !== undefined ? p.height - s.height : null;
    const state = p.ok === null ? 'belum dicek'
      : p.ok ? 'tinggi ' + p.height + (diff === 0 ? ' (sama)' : diff > 0 ? ' (+' + diff + ')' : ' (' + diff + ')') + ', terlihat ' + ago(p.seen)
      : esc(p.error || 'tidak terjangkau');
    return `<div class="item"><div class="l"><div class="t">${esc(p.url)}<span class="tagchip">${p.manual ? 'manual' : 'otomatis'}</span></div><div class="s">${state}</div></div>` +
      (ADMIN_TOKEN ? `<button class="btn ghost" type="button" data-remove="${esc(p.url)}" style="min-height:44px;padding:0 14px">Hapus</button>` : '') + '</div>';
  }).join('')
    : '<div class="empty">Belum ada peer. Tambahkan alamat node lain supaya blok dan transaksi saling tersinkron.</div>';
  rows('poolrows', [
    ['Transaksi menunggu', num(s.mempool.count, 0)],
    ['Total biaya menunggu', jab(s.mempool.fees)],
    ['Ukuran', bytes(s.mempool.bytes)],
  ]);
  if (!$('v-blok').hidden && listMode && listHeight !== s.height) loadList(true);
  if (chartHeight !== s.height) loadCharts(s);
}

async function loadCharts(s) {
  chartHeight = s.height;
  try {
    const d = await api('/api/chart?limit=60');
    const intervals = d.blocks.map((b) => b.interval);
    plot('c-time', [
      { data: intervals.map(() => s.targetBlockTime), color: 'var(--mute)', width: 2, dash: true },
      { data: intervals, color: 'var(--gold)' },
    ]);
    const diffs = d.blocks.map((b) => b.difficulty);
    plot('c-diff', [{ data: diffs, color: 'var(--blue)' }]);
    $('diffnote').textContent = diffs.length ? 'Terendah ' + num(Math.min(...diffs), 3) + ', tertinggi ' + num(Math.max(...diffs), 3) : '';
  } catch (e) { chartHeight = -1; }
}

async function tick() {
  try { render(await api('/api/stats')); }
  catch (e) { $('dot').classList.remove('on'); $('status').textContent = 'Offline'; }
}

const blockRow = (b) =>
  `<a class="item" href="#/blok/${b.index}"><div class="l"><div class="t">Blok ${b.index}</div><div class="s">${esc(short(b.hash, 12, 8))}</div></div>` +
  `<div class="r">${b.transfers ? b.transfers + ' transfer' : 'hanya hadiah'}<div class="mute">${b.interval !== null && b.interval !== undefined ? span(b.interval) + ', ' : ''}${ago(b.timestamp)}</div></div></a>`;

async function loadList(reset) {
  const before = reset ? (stats ? stats.height + 1 : 1) : listBefore;
  const data = await api('/api/list?limit=20&before=' + before);
  const html = data.blocks.map(blockRow).join('');
  if (reset) { $('blocks').innerHTML = html; listHeight = stats ? stats.height : -1; }
  else $('blocks').insertAdjacentHTML('beforeend', html);
  if (data.blocks.length) listBefore = data.blocks[data.blocks.length - 1].index;
  $('more').hidden = listBefore <= 0;
}

const txView = (t) => {
  const label = t.coinbase ? 'Hadiah penambang' : 'Transfer';
  const from = t.coinbase ? '<small>Dari</small><span class="mute">Hadiah blok baru</span>'
    : '<small>Dari</small>' + [...new Set(t.inputs.map((i) => i.address))].map(aLink).join('');
  const to = '<small>Ke</small>' + t.outputs.map((o) => `${aLink(o.address)}<span class="mute">${jab(o.amount)}</span>`).join('');
  return `<div class="tx"><div class="t"><b>${label}</b> <span class="mute">${jab(t.total)}${t.fee ? ', biaya ' + jab(t.fee) : ''}</span></div>` +
    `<a class="id" href="#/tx/${t.id}">${t.id}</a><div class="flow"><div>${from}</div><div>${to}</div></div></div>`;
};

async function showBlock(id) {
  const d = await api('/api/block/' + encodeURIComponent(id));
  const b = d.block;
  $('bdetail').innerHTML = `<h2 style="margin-top:6px">Blok ${b.index}</h2>` + [
    ['Konfirmasi', num(b.confirmations, 0)],
    ['Waktu', when(b.timestamp)],
    ['Selang dari blok sebelumnya', span(b.interval)],
    ['Penambang', aLink(b.miner)],
    ['Hadiah blok', jab(b.reward)],
    ['Biaya transaksi', jab(b.fees)],
    ['Total diklaim penambang', jab(b.claimed)],
    ['Jumlah transaksi', num(b.txCount, 0) + ' (' + num(b.transfers, 0) + ' transfer)'],
    ['Total output transaksi (termasuk kembalian)', jab(b.volume)],
    ['Ukuran blok', bytes(b.size)],
    ['Kesulitan', num(b.difficulty, 3)],
    ['Perkiraan hash dibutuhkan', count(b.estimatedHashes)],
    ['Target', esc(short(b.target, 12, 8)), true],
    ['Suplai setelah blok ini', jab(b.supplyAfter, 4)],
    ['Nonce', num(b.nonce, 0)],
    ['Hash', esc(b.hash), true],
    ['Hash sebelumnya', b.index > 0 ? `<a href="#/blok/${b.index - 1}">${esc(b.prevHash)}</a>` : esc(b.prevHash), true],
    ['Merkle root', esc(b.merkleRoot || 'blok format lama'), true],
    ['Format blok', esc(b.format)],
  ].map((r) => led(r[0], r[1], r[2])).join('') +
  `<h2>Transaksi <small>${d.txs.length}</small></h2>` + (d.txs.map(txView).join('') || '<div class="empty">Blok genesis tidak punya transaksi.</div>') +
  `<div style="display:flex;gap:10px;margin-top:16px">${b.index > 0 ? `<a class="btn ghost" style="display:inline-flex;align-items:center;text-decoration:none" href="#/blok/${b.index - 1}">Blok sebelumnya</a>` : ''}` +
  `${stats && b.index < stats.height ? `<a class="btn ghost" style="display:inline-flex;align-items:center;text-decoration:none" href="#/blok/${b.index + 1}">Blok berikutnya</a>` : ''}</div>`;
}

async function showTx(id) {
  const t = await api('/api/tx/' + encodeURIComponent(id));
  $('bdetail').innerHTML = '<h2 style="margin-top:6px">Transaksi</h2>' + [
    ['Status', t.status === 'confirmed' ? 'Terkonfirmasi (' + t.confirmations + ')' : 'Menunggu masuk blok'],
    ['Blok', t.height !== null ? `<a href="#/blok/${t.height}">${t.height}</a>` : '-'],
    ['Waktu', t.timestamp ? when(t.timestamp) : '-'],
    ['Jenis', t.coinbase ? 'Hadiah penambang' : 'Transfer'],
    ['Total', jab(t.total)],
    ['Biaya', jab(t.fee)],
    ['Jumlah input / output', t.inputs.length + ' / ' + t.outputs.length],
    ['Ukuran', bytes(t.size)],
    ['ID', esc(t.id), true],
  ].map((r) => led(r[0], r[1], r[2])).join('') +
  '<h2>Aliran dana</h2>' + txView(t);
}

async function showAddr(address) {
  const a = await api('/api/address/' + encodeURIComponent(address));
  $('bdetail').innerHTML = '<h2 style="margin-top:6px">Alamat</h2>' +
    `<div class="s" style="font:12px var(--mono);overflow-wrap:anywhere;margin-bottom:8px">${esc(a.address)}</div>` + [
    ['Saldo', jab(a.balance)],
    ['Bisa dikirim', jab(a.spendable)],
    ['Menunggu matang', jab(a.immature)],
    ['Pangsa suplai', pct(a.supplyShare, 4)],
    ['Peringkat pemegang', a.rank ? '#' + num(a.rank, 0) : '-'],
    ['Total masuk', jab(a.received)],
    ['Total keluar (termasuk biaya)', jab(a.sent)],
    ['Jumlah transaksi', num(a.txCount, 0)],
    ['Saldo belum terpakai (UTXO)', num(a.utxoCount, 0)],
    ['Blok ditambang', num(a.minedBlocks, 0)],
    ['Hadiah dari menambang', jab(a.minedAmount)],
    ['Pertama terlihat', when(a.firstSeen)],
    ['Terakhir terlihat', when(a.lastSeen)],
  ].map((r) => led(r[0], r[1])).join('') +
  '<h2>Riwayat <small>30 terakhir</small></h2>' + (a.history.map((h) =>
    `<a class="item" href="#/tx/${h.id}"><div class="l"><div class="t">${h.coinbase ? 'Hadiah penambang' : (h.delta >= 0 ? 'Masuk' : 'Keluar')}</div><div class="s">${esc(short(h.id, 12, 8))}, blok ${h.height}</div></div>` +
    `<div class="r ${h.delta >= 0 ? 'pos' : 'neg'}">${h.delta >= 0 ? '+' : ''}${jab(h.delta)}<div class="mute">${ago(h.timestamp)}</div></div></a>`).join('') || '<div class="empty">Belum ada transaksi.</div>');
}

$('searchform').addEventListener('submit', async (e) => {
  e.preventDefault();
  const q = $('q').value.trim();
  const note = $('searchnote');
  note.hidden = true;
  if (!q) return;
  try {
    if (/^\d+$/.test(q)) { await api('/api/block/' + q); location.hash = '#/blok/' + q; }
    else if (/^JAB/i.test(q)) location.hash = '#/alamat/' + q.replace(/^jab/i, 'JAB');
    else if (/^[0-9a-f]{64}$/i.test(q)) {
      try { await api('/api/block/' + q.toLowerCase()); location.hash = '#/blok/' + q.toLowerCase(); }
      catch (err) { await api('/api/tx/' + q.toLowerCase()); location.hash = '#/tx/' + q.toLowerCase(); }
    } else throw new Error('Isi dengan nomor blok, hash 64 karakter, atau alamat yang diawali JAB.');
  } catch (err) { note.textContent = err.message === 'tidak ditemukan' ? 'Tidak ditemukan di rantai ini.' : err.message; note.hidden = false; }
});
$('more').addEventListener('click', () => loadList(false).catch(() => {}));

$('sendform').addEventListener('submit', async (e) => {
  e.preventDefault();
  const note = $('sendnote'), button = $('sendbtn');
  button.disabled = true;
  try {
    const r = await api('/api/send', { to: $('to').value.trim(), amount: $('amount').value, fee: $('fee').value });
    note.className = 'note ok';
    note.innerHTML = `Transaksi terkirim dan menunggu masuk blok. <a href="#/tx/${r.id}">Lihat transaksi</a>`;
    $('to').value = ''; $('amount').value = '';
    tick();
  } catch (err) { note.className = 'note err'; note.textContent = err.message; }
  note.hidden = false; button.disabled = false;
});

$('peerform').addEventListener('submit', async (e) => {
  e.preventDefault();
  const note = $('peernote');
  try {
    await api('/api/peers', { url: $('peerurl').value });
    $('peerurl').value = ''; note.hidden = true; tick();
  } catch (err) { note.className = 'note err'; note.textContent = err.message; note.hidden = false; }
});
$('peers').addEventListener('click', async (e) => {
  const url = e.target.dataset && e.target.dataset.remove;
  if (url) { await api('/api/peers/remove', { url }).catch(() => {}); tick(); }
});
$('addr').addEventListener('click', async () => {
  const ok = await copyText($('addr').dataset.addr || '');
  const b = $('addr').querySelector('b');
  if (b) { b.textContent = ok ? 'tersalin' : 'gagal menyalin'; setTimeout(() => { b.textContent = 'salin'; }, 1500); }
});

async function loadPool() {
  try {
    const d = await api('/api/mempool');
    $('poolcount').textContent = d.txs.length;
    $('pool').innerHTML = d.txs.length ? d.txs.map(txView).join('') : '<div class="empty">Tidak ada transaksi yang menunggu.</div>';
  } catch (e) {}
}

async function route() {
  const parts = (location.hash.replace(/^#\/?/, '') || 'ringkasan').split('/');
  const name = parts[0];
  const tabs = ['ringkasan', 'blok', 'tambang', 'kirim', 'jaringan'];
  const tab = ['tx', 'alamat'].includes(name) ? 'blok' : (tabs.includes(name) ? name : 'ringkasan');
  document.querySelectorAll('section.view').forEach((s) => { s.hidden = s.id !== 'v-' + tab; });
  document.querySelectorAll('nav a').forEach((a) => {
    if (a.dataset.tab === tab) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current');
  });
  window.scrollTo(0, 0);
  if (tab === 'blok') {
    const detail = name !== 'blok' || parts[1];
    listMode = !detail;
    $('blist').hidden = !!detail;
    $('bdetail').hidden = !detail;
    try {
      if (!detail) await loadList(true);
      else if (name === 'tx') await showTx(parts[1]);
      else if (name === 'alamat') await showAddr(parts[1]);
      else await showBlock(parts[1]);
    } catch (err) { $('bdetail').innerHTML = `<div class="note err">${esc(err.message === 'tidak ditemukan' ? 'Tidak ditemukan di rantai ini.' : err.message)}</div>`; }
  } else if (tab === 'jaringan') loadPool();
}
if (!ADMIN_TOKEN) {
  $('sendform').hidden = true;
  $('peerform').hidden = true;
  $('sendnote').className = 'note';
  $('sendnote').textContent = 'Kirim JAB dan kelola peer hanya bisa dari perangkat pemilik node. Buka dashboard lewat http://127.0.0.1:' + location.port + ' di perangkat yang menjalankan node ini.';
  $('sendnote').hidden = false;
}
window.addEventListener('hashchange', route);
tick().then(route);
setInterval(tick, 2000);
setInterval(() => { if (!$('v-jaringan').hidden) loadPool(); }, 4000);
</script>
</body>
</html>
"""


if __name__ == '__main__':
    main()

