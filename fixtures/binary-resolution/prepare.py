#!/usr/bin/env python3
"""Development-only javac/JVM witness producer; Rust consumes sealed bytes."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
JDK = Path('/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    source = (HERE / 'Resolution.java').read_bytes()
    javac, java = JDK / 'bin/javac', JDK / 'bin/java'
    jmod = JDK / 'jmods/java.base.jmod'
    manifest = {
        'schema': 'rust-selector-jvm-resolution-fixture/v1',
        'source_sha256': digest(source),
        'javac': str(javac), 'javac_sha256': digest(javac.read_bytes()),
        'java': str(java), 'java_sha256': digest(java.read_bytes()),
        'java_version': subprocess.check_output([str(java), '-version'], stderr=subprocess.STDOUT, text=True),
        'compile_command': ['javac', '--release', '17', '-g:none', '-d', '<classes>', 'Resolution.java'],
        'java_base_jmod': str(jmod), 'java_base_jmod_sha256': digest(jmod.read_bytes()),
        'object_class_member': 'classes/java/lang/Object.class',
        'synthetic_controls': [], 'outputs': [],
    }
    with tempfile.TemporaryDirectory(prefix='rust-selector-resolution-') as tmp:
        classes = Path(tmp) / 'classes'
        subprocess.run([str(javac), '--release', '17', '-g:none', '-d', str(classes), str(HERE / 'Resolution.java')], check=True, capture_output=True)
        witness = subprocess.check_output([str(java), '-cp', str(classes), 'fixture.Resolution'], text=True)
        manifest['jvm_witness'] = witness
        for entry in sorted(classes.rglob('*.class')):
            target = HERE / 'classes' / entry.relative_to(classes)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(entry.read_bytes())
    with zipfile.ZipFile(jmod) as archive:
        target = HERE / 'classes/java/lang/Object.class'
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(archive.read('classes/java/lang/Object.class'))
    source_zip = JDK / 'lib/src.zip'
    with zipfile.ZipFile(source_zip) as archive:
        target = HERE / 'jdk-source/java/lang/Object.java'
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(archive.read('java.base/java/lang/Object.java'))
    manifest['jdk_source_zip_sha256'] = digest(source_zip.read_bytes())
    for name in ('LICENSE', 'ADDITIONAL_LICENSE_INFO', 'ASSEMBLY_EXCEPTION'):
        (HERE / name).write_bytes((JDK / 'legal/java.base' / name).read_bytes())
    # Deliberately invalid source hierarchy: two unrelated concrete defaults.
    # Same-width constant-pool name replacement preserves classfile encoding.
    original = (HERE / 'classes/fixture/DefaultLeaf.class').read_bytes()
    before, after = b'fixture/DefaultTop', b'fixture/DefaultTwo'
    assert len(before) == len(after) and original.count(before) == 1
    control = original.replace(before, after)
    path = HERE / 'controls/ambiguous-default.class'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(control)
    manifest['synthetic_controls'].append({
        'path': path.relative_to(HERE).as_posix(), 'source': 'classes/fixture/DefaultLeaf.class',
        'transform': 'replace one equal-length UTF8 constant fixture/DefaultTop with fixture/DefaultTwo',
        'expected': 'ambiguous maximally specific concrete interface methods; no arbitrary choice',
        'sha256': digest(control),
    })
    original = (HERE / 'classes/fixture/DefaultOne.class').read_bytes()
    assert original.count(b'fixture/DefaultTop') == 1
    cyclic = original.replace(b'fixture/DefaultTop', b'fixture/DefaultOne')
    cycle_path = HERE / 'controls/cyclic-interface.class'
    cycle_path.write_bytes(cyclic)
    manifest['synthetic_controls'].append({
        'path': cycle_path.relative_to(HERE).as_posix(), 'source': 'classes/fixture/DefaultOne.class',
        'transform': 'replace one equal-length UTF8 superinterface fixture/DefaultTop with fixture/DefaultOne',
        'expected': 'invalid cyclic interface hierarchy; explicit unknown', 'sha256': digest(cyclic),
    })
    with zipfile.ZipFile(HERE / 'resolution.jar', 'w') as archive:
        for entry in sorted((HERE / 'classes').rglob('*.class')):
            info = zipfile.ZipInfo(entry.relative_to(HERE / 'classes').as_posix(), (2026, 11, 6, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, entry.read_bytes())
    for entry in sorted([*(HERE / 'classes').rglob('*.class'), HERE / 'resolution.jar', path, cycle_path,
                         HERE / 'jdk-source/java/lang/Object.java', HERE / 'LICENSE',
                         HERE / 'ADDITIONAL_LICENSE_INFO', HERE / 'ASSEMBLY_EXCEPTION']):
        raw = entry.read_bytes()
        manifest['outputs'].append({'path': entry.relative_to(HERE).as_posix(), 'sha256': digest(raw), 'bytes': len(raw)})
    (HERE / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(witness, end='')


if __name__ == '__main__':
    main()
