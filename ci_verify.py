#!/usr/bin/env python3
"""Reproduce the recorded build with the pinned Lean and mathlib commit."""
from pathlib import Path
import json, os, re, subprocess, tempfile, urllib.request

def main():
    repo=Path(__file__).resolve().parent
    environment=json.loads((repo/'evidence/environment.json').read_text())
    commit=environment['mathlib_commit']
    if not re.fullmatch(r'[0-9a-f]{40}',commit):
        raise RuntimeError('Invalid recorded mathlib commit')
    env=dict(os.environ)
    env['PATH']=str(Path.home()/'.elan/bin')+os.pathsep+env.get('PATH','')
    def run(args,cwd):
        print('RUN',*map(str,args),flush=True)
        subprocess.run(list(map(str,args)),cwd=cwd,env=env,check=True)
    with tempfile.TemporaryDirectory(prefix='a220119-check-')as tmp:
        work=Path(tmp)
        elan=Path.home()/'.elan/bin/elan'
        if not elan.exists():
            installer=work/'elan-init.sh'
            url='https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh'
            with urllib.request.urlopen(url,timeout=60)as response:
                installer.write_bytes(response.read())
            run(['sh',installer,'-y','--no-modify-path','--default-toolchain','none'],work)
        run([elan,'toolchain','install','leanprover/lean4:v4.19.0'],work)
        mathlib=work/'mathlib';mathlib.mkdir()
        run(['git','init',mathlib],work)
        run(['git','remote','add','origin','https://github.com/leanprover-community/mathlib4.git'],mathlib)
        run(['git','fetch','--depth','1','origin',commit],mathlib)
        run(['git','checkout','--detach','FETCH_HEAD'],mathlib)
        if (mathlib/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.19.0':
            raise RuntimeError('Recorded dependency does not use the expected Lean release')
        run(['lake','exe','cache','get'],mathlib)
        run(['lake','env','python3',repo/'source/compile_in_lake.py'],mathlib)

if __name__=='__main__':
    main()
