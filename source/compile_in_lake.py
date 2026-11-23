#!/usr/bin/env python3
"""Invoked with `lake env python3 ...` inside the pinned mathlib checkout."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent
RUNNER_VERSION=3
LEAN=['lean',f'--root={ROOT}','-j1']
LOG=ROOT/'logs';LOG.mkdir(exist_ok=True)
ORDER=['A220119/Spec.lean','A220119/Arithmetic.lean',
       'A220119/PolynomialTools.lean','A220119/Elimination.lean',
       'A220119/Main.lean','Audit.lean']
STATUS=ROOT/'status.json'
report={'verified':False,'state':'STARTED','compiled':[],'errors':[],
        'runner_version':RUNNER_VERSION,'source_root':str(ROOT),
        'expected_mathlib_tag':'v4.19.0','ordinary_lean_kernel_check':True,
        'independent_kernel_checker_used':False}

def save():
    STATUS.write_text(json.dumps(report,indent=2)+'\n')

def run(cmd,logfile,timeout=900):
    print('RUN', ' '.join(map(str,cmd)),flush=True)
    # Lake supplies relative search paths: preserve the mathlib working directory.
    result=subprocess.run(cmd,cwd=Path.cwd(),env=ENV,text=True,stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,timeout=timeout)
    logfile.write_text(result.stdout)
    print(result.stdout,flush=True)
    if result.returncode:
        raise RuntimeError(f'Exit {result.returncode}; see {logfile.name}')
    return result.stdout

ENV=dict(os.environ)
ENV['LEAN_PATH']=str(ROOT)+os.pathsep+ENV.get('LEAN_PATH','')
ENV['NO_COLOR']='1';ENV['TERM']='dumb'
save()
try:
    # Refuse to silently replace the trusted mathematical target or its audit.
    expected=json.loads((ROOT/'source_manifest.json').read_text())
    for name in ['A220119/Spec.lean','Audit.lean']:
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected[name]:
            raise RuntimeError(f'Trusted target changed: {name}')
    forbidden=re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide)\b')
    for name in ORDER:
        source=(ROOT/name).read_text()
        # Strip nested block comments and line comments before lexical checks.
        i=0;depth=0;clean=[]
        while i<len(source):
            if source.startswith('/-',i):depth+=1;i+=2;continue
            if depth and source.startswith('-/',i):depth-=1;i+=2;continue
            if depth:i+=1;continue
            if source.startswith('--',i):
                end=source.find('\n',i);i=len(source)if end<0 else end;continue
            clean.append(source[i]);i+=1
        found=forbidden.findall(''.join(clean))
        if found:raise RuntimeError(f'Forbidden proof construct in {name}: {found}')
    report['lean_version']=run(['lean','--version'],LOG/'lean_version.log').strip()
    if not re.search(r'\b4\.19\.0\b', report['lean_version']):
        raise RuntimeError('Compiler version does not match the pinned toolchain')
    # Check the package root and Mathlib imports before attempting proof modules.
    smoke=ROOT/'ImportSmoke.lean'
    smoke.write_text('import Mathlib\n#check Nat.choose\n')
    run(LEAN+[str(smoke)],LOG/'import_smoke.log')
    report['import_smoke_passed']=True;save()
    for name in ORDER:
        dst=ROOT/name
        run(LEAN+['-o',str(dst.with_suffix('.olean')),str(dst)],
            LOG/(name.replace('/','_')+'.log'))
        report['compiled'].append(name);save()
    # This file contains the separately written original polynomial statement.
    audit=run(LEAN+[str(ROOT/'Audit.lean')],LOG/'axiom_audit.log')
    if 'sorryAx' in audit:raise RuntimeError('Audit found an admitted declaration')
    allowed={'propext','Classical.choice','Quot.sound'}
    dependency_lists=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',audit,re.S)
    for values in dependency_lists:
        names={v.strip()for v in values.split(',')if v.strip()}
        if not names<=allowed:raise RuntimeError(f'Unexpected axioms: {names-allowed}')
    for name in ['A220119.constantTerm_eq_doubleSum','A220119.full_conjecture',
                 'IndependentAudit.original_statement']:
        if name not in audit:raise RuntimeError(f'Missing audit report for {name}')
    report['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                             for name in ORDER}
    report['verified']=True;report['state']='VERIFIED_BY_COLAB_RUN'
except Exception as error:
    report['state']='NOT_VERIFIED';report['errors'].append(str(error))
    print('NOT VERIFIED:',error,flush=True)
finally:
    save();print(json.dumps(report,indent=2),flush=True)
sys.exit(0 if report['verified']else 1)
