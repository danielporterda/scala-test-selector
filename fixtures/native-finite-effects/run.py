#!/usr/bin/env python3
"""Benchmark-only genuine JVM controls. No Rust, sbt, or selector query runs."""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[1]
sys.path.insert(0, str(WORKSPACE/'tools'))
from runtime_acceptance import measure

EXPECTED = (
    'loads:all-nine\nnew-and-length:all-types\nstores:all-nine\n'
    'null-load:NullPointerException\nbounds-load:ArrayIndexOutOfBoundsException\n'
    'null-length:NullPointerException\nnegative-new:NegativeArraySizeException\n'
    'zero-divide:ArithmeticException\nzero-remainder:ArithmeticException\n'
    'handlers:7:7:-1:-1:-1:callbacks=4:shared=4\n'
    'native:UnsatisfiedLinkError\n'
    'consumers:later-store-call:callback:monitor:native:reflection:dynamic:throw-identity\n'
)


def pin(path):
    path = Path(path).resolve()
    digest = hashlib.sha256()
    with path.open('rb') as file:
        for block in iter(lambda:file.read(1024*1024), b''):
            digest.update(block)
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':digest.hexdigest()}


def verify():
    record = json.loads((HERE/'manifest.json').read_text())
    for expected in record['inputs']+record['files']:
        assert pin(expected['path']) == expected, expected['path']
    subprocess.run([sys.executable,str(HERE/'inventory_check.py'),'--verify'],check=True)
    with zipfile.ZipFile(HERE/'bytecode.jar') as jar:
        expected = {p.relative_to(HERE/'classes').as_posix():p for p in (HERE/'classes').rglob('*.class')}
        assert len(jar.namelist()) == len(set(jar.namelist())) and set(jar.namelist()) == set(expected)
        for name,path in expected.items():
            assert jar.read(name) == path.read_bytes(), name
    print('All JVM fixture, producer, classpath and exact class-inventory pins verified')


def prepare():
    assert not (HERE/'manifest.json').exists(), 'preserve first attempt; use --verify after freezing'
    platform_path = WORKSPACE/'artifacts/pr7743-declared-runtime-platform-v2/head/manifest.json'
    platform = json.loads(platform_path.read_text())
    home = Path(platform['image']['canonical_home'])
    java, javac = home/'bin/java', home/'bin/javac'
    files = [Path(__file__), HERE/'inventory_check.py', WORKSPACE/'tools/runtime_acceptance.py',
             *sorted((HERE/'src').rglob('*.java')), platform_path,
             java,javac,home/'release',home/'lib/modules',home/'lib/ct.sym']
    before = [pin(path) for path in files]
    for name in ['launcher','modules','release']:
        expected = platform['image'][name]
        assert pin(expected['path']) == expected, name
    classes = HERE/'classes';classes.mkdir(exist_ok=True)
    measurements = []

    def execute(command,label):
        result = measure(list(map(str,command)),HERE,label,cwd=WORKSPACE)
        measurements.append(result)
        (HERE/'attempt.json').write_text(json.dumps({'schema':'selector-jvms-fixture-attempt/v1',
            'inputs':before,'measurements':measurements,'complete':False},separators=(',',':'))+'\n')
        if result['exit_code']:
            raise RuntimeError(label+' failed; attempt/logs preserved')

    execute([java,'-version'],'java-version')
    execute([javac,'--release','17','-g:none','-d',classes,*sorted((HERE/'src').rglob('*.java'))],'compile')
    execute([java,'-Xmx64m','-cp',classes,'finitecase.Check'],'correctness')
    assert (HERE/'correctness.stdout').read_text() == EXPECTED
    execute([sys.executable,HERE/'inventory_check.py'],'inventory')
    execute([java,'-Xmx64m','-Xint','-cp',classes,'finitecase.Warm','3000'],'warm-interpreter')
    execute([java,'-Xmx64m','-Xbatch','-cp',classes,'finitecase.Warm','80000'],'warm-default')
    # No optimization identity, reuse count, or stack length is a pass condition.
    with zipfile.ZipFile(HERE/'bytecode.jar','w') as jar:
        for path in sorted(classes.rglob('*.class')):
            info=zipfile.ZipInfo(path.relative_to(classes).as_posix(),(1980,1,1,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            jar.writestr(info,path.read_bytes())
    after = [pin(path) for path in files]
    assert before == after, 'frozen inputs changed during fixture generation'
    record = {'schema':'selector-jvms-finite-effects-benchmark/v1','complete':True,
        'diagnostic_only':True,'omission_authority':False,
        'scope':'Genuine javac/JVM controls; no Rust/sbt/project query, no VM exception freshness assumption, no production effect certificate.',
        'classpath':{'compile':'--release 17 via pinned ct.sym; no user classpath',
                     'runtime':'only generated classes plus pinned runtime image'},
        'inherited_java_environment':{k:os.environ.get(k) for k in ['JAVA_TOOL_OPTIONS','JDK_JAVA_OPTIONS','_JAVA_OPTIONS']},
        'inputs':before,'measurements':measurements,'expected_correctness_stdout':EXPECTED,
        'optimization_observations':{mode:(HERE/(mode+'.stdout')).read_text() for mode in ['warm-interpreter','warm-default']},
        'observation_limit':'Reported identities/VM flags do not prove all runtime behavior or freshness; reuse is not required for correctness.',
        'files':[pin(path) for path in sorted(HERE.rglob('*')) if path.is_file() and
                 path.name not in ['manifest.json','attempt.json'] and '__pycache__' not in path.parts]}
    (HERE/'manifest.json').write_text(json.dumps(record,separators=(',',':'))+'\n')
    verify()


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    verify() if args.verify else prepare()
