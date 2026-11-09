#!/usr/bin/env python3
"""Development-only javac fixture production; Rust tests load checked-in bytes."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
JAVAC = Path('/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home/bin/javac')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def archive(path, classes, compression):
    with zipfile.ZipFile(path, 'w', compression=compression) as jar:
        for item in sorted(classes.rglob('*.class')):
            info = zipfile.ZipInfo(item.relative_to(classes).as_posix(), (2026, 11, 6, 0, 0, 0))
            info.compress_type = compression
            jar.writestr(info, item.read_bytes())


def main():
    original = (HERE / 'Probe.java').read_bytes()
    producer = {'schema': 'rust-selector-native-jvm-fixture/v1', 'javac': str(JAVAC),
        'javac_sha256': digest(JAVAC.read_bytes()),
        'javac_version': subprocess.check_output([str(JAVAC), '-version'], text=True, stderr=subprocess.STDOUT).strip(),
        'source_sha256': digest(original), 'product_tests_executed': False, 'outputs': []}
    with tempfile.TemporaryDirectory(prefix='rust-selector-jvm-fixture-') as temporary:
        root = Path(temporary)
        for variant, source in [('original', original), ('alternate', original.replace(
                b'public static Made make(Runnable callback) { return new Made(callback); }',
                b'public static Made make(Runnable callback) { return null; }'))]:
            folder = root / variant
            classes = folder / 'classes'
            classes.mkdir(parents=True)
            path = folder / 'Probe.java'
            path.write_bytes(source)
            command = [str(JAVAC), '--release', '17', '-g:none', '-d', str(classes), str(path)]
            subprocess.run(command, check=True, capture_output=True)
            if variant == 'original':
                for item in sorted(classes.rglob('*.class')):
                    target = HERE / 'classes' / item.relative_to(classes)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(item.read_bytes())
                archive(HERE / 'fixture-stored.jar', classes, zipfile.ZIP_STORED)
                archive(HERE / 'fixture-deflated.jar', classes, zipfile.ZIP_DEFLATED)
            else:
                archive(HERE / 'fixture-alternate.jar', classes, zipfile.ZIP_STORED)
            producer.setdefault('commands', []).append({'variant': variant,
                'command_template': ['javac', '--release', '17', '-g:none', '-d', '<classes>', '<Probe.java>'],
                'source_sha256': digest(source), 'exit_code': 0})
    for path in sorted([*HERE.glob('*.jar'), *(HERE / 'classes').rglob('*.class')]):
        raw = path.read_bytes()
        producer['outputs'].append({'path': path.relative_to(HERE).as_posix(), 'bytes': len(raw), 'sha256': digest(raw)})
    (HERE / 'manifest.json').write_text(json.dumps(producer, indent=2) + '\n')
    print(json.dumps({'classfiles': len(list((HERE / 'classes').rglob('*.class'))), 'jars': 3}))


if __name__ == '__main__':
    main()
