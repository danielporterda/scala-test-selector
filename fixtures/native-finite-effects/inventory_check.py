#!/usr/bin/env python3
"""Independent bounded class-wire inventory; not a JVM stack/type verifier."""
import argparse
import hashlib
import json
import struct
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


class Reader:
    def __init__(self, data):
        self.data, self.at = data, 0

    def take(self, count):
        if count < 0 or self.at + count > len(self.data):
            raise ValueError('truncated class wire')
        old = self.at
        self.at += count
        return self.data[old:self.at]

    def number(self, count):
        return int.from_bytes(self.take(count), 'big')


def inventory(data, expected_owner='finitecase/Probe'):
    if len(data) > 128 * 1024:
        raise ValueError('class budget')
    r = Reader(data)
    if r.take(4) != b'\xca\xfe\xba\xbe':
        raise ValueError('magic')
    minor, major = r.number(2), r.number(2)
    pool = [None] * r.number(2)
    index = 1
    while index < len(pool):
        tag = r.number(1)
        if tag == 1:
            value = r.take(r.number(2)).decode('utf-8')
        elif tag in (3, 4):
            value = r.take(4).hex()
        elif tag in (5, 6):
            value = r.take(8).hex()
        elif tag in (7, 8, 16, 19, 20):
            value = r.number(2)
        elif tag in (9, 10, 11, 12, 17, 18):
            value = (r.number(2), r.number(2))
        elif tag == 15:
            value = (r.number(1), r.number(2))
        else:
            raise ValueError('constant pool tag')
        pool[index] = (tag, value)
        index += 2 if tag in (5, 6) else 1
    if index != len(pool):
        raise ValueError('wide pool slot')

    def cp(index, tags):
        if not 0 < index < len(pool) or pool[index] is None or pool[index][0] not in tags:
            raise ValueError('constant pool reference')
        return pool[index][1]

    def text(index):
        return cp(index, {1})

    def owner(index):
        return text(cp(index, {7}))

    def member(index, tags):
        c, nt = cp(index, tags)
        name, descriptor = cp(nt, {12})
        return [owner(c), text(name), text(descriptor)]

    def attributes(source):
        attrs = []
        for _ in range(source.number(2)):
            name = text(source.number(2))
            length = source.number(4)
            at = source.at
            attrs.append((name, source.take(length), at))
        return attrs

    flags, this, parent = r.number(2), r.number(2), r.number(2)
    name = owner(this)
    if name != expected_owner:
        raise ValueError('class owner')
    parents = ([owner(parent)] if parent else []) + [owner(r.number(2)) for _ in range(r.number(2))]
    fields = []
    for _ in range(r.number(2)):
        access, n, d = r.number(2), text(r.number(2)), text(r.number(2))
        attributes(r)
        fields.append([n, d, access])
    methods, code_locations = [], []
    for _ in range(r.number(2)):
        access, n, d = r.number(2), text(r.number(2)), text(r.number(2))
        attrs = attributes(r)
        code_attrs = [(blob, at) for attr, blob, at in attrs if attr == 'Code']
        if len(code_attrs) > 1 or bool(access & (0x100 | 0x400)) == bool(code_attrs):
            raise ValueError('method Code/flags')
        method = {'name': n, 'descriptor': d, 'flags': access}
        if code_attrs:
            blob, absolute = code_attrs[0]
            c = Reader(blob)
            method['stack'], method['locals'] = c.number(2), c.number(2)
            code_len = c.number(4)
            if not 0 < code_len <= 65535:
                raise ValueError('code budget')
            code_abs = absolute + c.at
            code = c.take(code_len)
            handlers = [[c.number(2), c.number(2), c.number(2), c.number(2)] for _ in range(c.number(2))]
            attributes(c)
            if c.at != len(blob):
                raise ValueError('Code trailing bytes')
            method['code_bytes'], method['code_sha256'] = code_len, sha(code)
            method['_code'], method['_handlers'] = code, handlers
            code_locations.append((method, code_abs))
        methods.append(method)
    attrs = attributes(r)
    if r.at != len(data) or len(methods) > 256:
        raise ValueError('class geometry/budget')
    bootstraps = []
    for attr, blob, _ in attrs:
        if attr != 'BootstrapMethods':
            continue
        b = Reader(blob)
        for _ in range(b.number(2)):
            kind, ref = cp(b.number(2), {15})
            target = member(ref, {10, 11})
            arguments = [b.number(2) for _ in range(b.number(2))]
            for argument in arguments:
                cp(argument, {3, 4, 5, 6, 7, 8, 15, 16, 17})
            bootstraps.append([kind, target])
        if b.at != len(blob):
            raise ValueError('bootstrap geometry')

    for method, code_abs in code_locations:
        code = method.pop('_code')
        instructions, branches, calls, field_ops = [], [], [], []
        pc = 0
        while pc < len(code):
            at, op = pc, code[pc]
            pc += 1
            operand = None
            if op in (16, 18, 188) or 21 <= op <= 25 or 54 <= op <= 58 or op == 169:
                size = 1
            elif op in (17, 19, 20, 132) or 153 <= op <= 168 or 178 <= op <= 184 or op in (187, 189, 192, 193, 198, 199):
                size = 2
            elif op == 197:
                size = 3
            elif op in (185, 186, 200, 201):
                size = 4
            elif op == 196:
                if pc >= len(code) or code[pc] not in (21, 22, 23, 24, 25, 54, 55, 56, 57, 58, 132, 169):
                    raise ValueError('wide opcode')
                size = 5 if code[pc] == 132 else 3
            elif op in (170, 171):
                pad = (-pc) % 4
                if any(code[pc:pc + pad]):
                    raise ValueError('switch padding')
                table = Reader(code[pc + pad:])
                signed = lambda: int.from_bytes(table.take(4), 'big', signed=True)
                destinations = [at + signed()]
                if op == 170:
                    low, high = signed(), signed()
                    count = high - low + 1
                    if not 0 < count <= 65535:
                        raise ValueError('switch count')
                    destinations += [at + signed() for _ in range(count)]
                else:
                    count = signed()
                    if not 0 <= count <= 65535:
                        raise ValueError('switch count')
                    keys = []
                    for _ in range(count):
                        keys.append(signed()); destinations.append(at + signed())
                    if any(x >= y for x, y in zip(keys, keys[1:])):
                        raise ValueError('switch keys')
                size = pad + table.at
                branches.extend([at, target] for target in destinations)
            elif 0 <= op <= 201 and op not in (202,):
                size = 0
            else:
                raise ValueError('reserved opcode')
            if pc + size > len(code):
                raise ValueError('instruction truncation')
            if 153 <= op <= 168 or op in (198, 199, 200, 201):
                branches.append([at, at + int.from_bytes(code[pc:pc + size], 'big', signed=True)])
            if op in (18, 19, 20):
                operand = int.from_bytes(code[pc:pc + size], 'big')
                cp(operand, {3, 4, 5, 6, 7, 8, 15, 16, 17})
            if op == 188 and code[pc] not in range(4, 12):
                raise ValueError('primitive array type')
            if op in (187, 189, 192, 193, 197):
                owner(int.from_bytes(code[pc:pc + 2], 'big'))
            if 178 <= op <= 186:
                operand = int.from_bytes(code[pc:pc + 2], 'big')
                if op <= 181:
                    field_ops.append([at, op, *member(operand, {9})])
                elif op <= 185:
                    calls.append([at, op, *member(operand, {10, 11})])
                    if op == 185 and (not code[pc + 2] or code[pc + 3]):
                        raise ValueError('invokeinterface suffix')
                else:
                    bootstrap, nt = cp(operand, {18})
                    if bootstrap >= len(bootstraps) or code[pc + 2:pc + 4] != b'\0\0':
                        raise ValueError('invokedynamic bootstrap')
                    n, d = cp(nt, {12})
                    calls.append([at, op, '<dynamic>', text(n), text(d), bootstraps[bootstrap]])
            instructions.append([at, op])
            pc += size
        starts = {at for at, _ in instructions}
        if any(target not in starts for _, target in branches):
            raise ValueError('branch target boundary')
        handlers = method.pop('_handlers')
        for start, end, target, catch in handlers:
            if not start < end <= len(code) or start not in starts or end not in starts | {len(code)} or target not in starts:
                raise ValueError('handler boundary')
            if catch:
                owner(catch)
        method.update(instructions=instructions, branches=branches, calls=calls, field_ops=field_ops,
                      handlers=[[start, end, target, owner(catch) if catch else '*'] for start, end, target, catch in handlers])
    result = {'owner': name, 'class_sha256': sha(data), 'bytes': len(data), 'class_version': [major, minor],
              'flags': flags, 'parents': parents, 'fields': fields, 'methods': methods,
              'scope': 'structural fixture inventory only; not stack/type verification or omission authority'}
    return result, code_locations


EXPECTED = {'readInt':46, 'readLong':47, 'readFloat':48, 'readDouble':49, 'readReference':50,
            'readByte':51, 'readBoolean':51, 'readChar':52, 'readShort':53,
            'writeInt':79, 'writeLong':80, 'writeFloat':81, 'writeDouble':82, 'writeReference':83,
            'writeByte':84, 'writeBoolean':84, 'writeChar':85, 'writeShort':86,
            'divideInt':108, 'divideLong':109, 'remainderInt':112, 'remainderLong':113,
            'length':190, 'referenceLength':190, 'newReference':189,
            'newMultiPrimitive':197, 'newMultiReference':197}


def check_matrix(result):
    methods = {row['name']: row for row in result['methods']}
    for name, opcode in EXPECTED.items():
        assert opcode in [op for _, op in methods[name]['instructions']], name
    for name in ['newBoolean','newByte','newChar','newShort','newInt','newLong','newFloat','newDouble']:
        assert 188 in [op for _, op in methods[name]['instructions']], name
    assert methods['opaque']['flags'] & 0x100 and 'code_bytes' not in methods['opaque']
    for name in ['branchAndCatch','catchDivision','catchNegative']:
        method = methods[name]
        assert method['handlers'], name
        assert any(call[2:4] == ['java/lang/Runnable','run'] for call in method['calls']), name
        assert any(row[1] == 179 and row[3] == 'shared' for row in method['field_ops']), name
    assert methods['branchAndCatch']['branches']
    assert any(call[2:4] == ['finitecase/Probe','after'] for call in methods['writeAfterAllocation']['calls'])
    assert any(call[1] == 186 and call[5][1][0] == 'java/lang/invoke/StringConcatFactory' for call in methods['dynamicAfterRead']['calls'])


def self_test(data):
    result, locations = inventory(data)
    check_matrix(result)
    mutants = [('truncated', data[:-1])]
    first, absolute = locations[0]
    changed = bytearray(data); changed[absolute] = 202
    mutants.append(('reserved', bytes(changed)))
    for method, absolute in locations:
        branch = next((pc for pc, op in method['instructions'] if 153 <= op <= 168), None)
        if branch is not None:
            changed = bytearray(data); struct.pack_into('>h', changed, absolute + branch + 1, 1)
            mutants.append(('branch-into-operand', bytes(changed))); break
    for method, absolute in locations:
        if method['handlers']:
            changed = bytearray(data); struct.pack_into('>H', changed, absolute + method['code_bytes'] + 6, method['code_bytes'])
            mutants.append(('handler-at-code-end', bytes(changed))); break
    for label, changed in mutants:
        try:
            inventory(changed)
        except (ValueError, IndexError, UnicodeDecodeError):
            continue
        raise AssertionError('malformed synthetic control accepted: ' + label)
    return [label for label, _ in mutants]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    data = (ROOT/'classes/finitecase/Probe.class').read_bytes()
    result, _ = inventory(data)
    check_matrix(result)
    controls = self_test(data)
    output = {'schema':'selector-jvms-fixture-inventory/v1', 'diagnostic_only':True,
              'omission_authority':False, 'synthetic_rejection_controls':controls, 'class':result}
    path = ROOT/'inventory.json'
    if args.verify:
        assert json.loads(path.read_text()) == output
        print('Independent finite-effects inventory and four malformed controls verified')
    else:
        path.write_text(json.dumps(output,separators=(',',':'))+'\n')


if __name__ == '__main__':
    main()
