#!/usr/bin/env python3
"""Create a public proof repository from a SUCCESSFUL, unchanged Colab run.

Run through the supplied Colab cell, which passes ASSET_BYTES for the complete
uploaded asset ZIP. Credentials are requested with getpass and never saved.
"""
from pathlib import Path
from urllib import request, error, parse
import base64, getpass, hashlib, html, io, json, re, subprocess, time, zipfile

ORDER=['A220119/Spec.lean','A220119/Arithmetic.lean',
       'A220119/PolynomialTools.lean','A220119/Elimination.lean',
       'A220119/Main.lean','Audit.lean']
THEOREMS=['A220119.constantTerm_eq_doubleSum','A220119.full_conjecture',
          'IndependentAudit.original_statement']

def checked_sources(base):
    source=base/'source'
    status=json.loads((source/'status.json').read_text())
    if status.get('verified')is not True or status.get('state')!='VERIFIED_BY_COLAB_RUN':
        raise RuntimeError('Nothing uploaded: the complete Lean build and audit have not passed.')
    if status.get('compiled')!=ORDER:
        raise RuntimeError('Nothing uploaded: the record does not contain all six compiled modules.')
    files={name:(source/name).read_bytes()for name in ORDER}
    for name,data in files.items():
        if hashlib.sha256(data).hexdigest()!=status.get('source_sha256',{}).get(name):
            raise RuntimeError('Nothing uploaded: source changed after verification: '+name)
    audit=(source/'logs/axiom_audit.log').read_text()
    if 'sorryAx'in audit or not all(name in audit for name in THEOREMS):
        raise RuntimeError('Nothing uploaded: the expected axiom audit is missing or failed.')
    allowed={'propext','Classical.choice','Quot.sound'}
    for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',audit,re.S):
        names={x.strip()for x in group.split(',')if x.strip()}
        if not names<=allowed:raise RuntimeError('Unexpected axioms in audit')
    return source,status,files

def package(base,asset_bytes,author):
    source,status,modules=checked_sources(base)
    out={}
    with zipfile.ZipFile(io.BytesIO(asset_bytes))as archive:
        def asset(name):return archive.read('A220119_Lean/'+name)
        original_manifest=json.loads(asset('source_manifest.json'))
        for name in ['A220119/Spec.lean','Audit.lean']:
            if hashlib.sha256(modules[name]).hexdigest()!=original_manifest[name]:
                raise RuntimeError('The mathematical target or original-statement audit changed; no repository created.')
        proof=archive.read('written_proof/A220119_proof.md').decode()
        proof=proof.replace('Working note, 23 November 2026.',
            f'Contributor: {author}. Substantial OpenAI ChatGPT/Codex assistance was used.\n\n'
            'Working note, 23 November 2026.')
        proof=proof.replace(
            'No Lean verification or\nexternal peer review is claimed.',
            'The accompanying Lean formalization passed the recorded Lean 4.19.0\n'
            'build and exact-statement/axiom audit. Independent human peer review is not claimed.')
        proof=proof.replace('Nothing has been submitted or posted externally.',
                            'Publication and verification details are recorded in the repository README and evidence.')
        out['paper/PROOF.md']=proof.encode()
        tex=archive.read('written_proof/A220119_proof.tex').decode()
        escapes={'\\':r'\textbackslash{}','{':r'\{','}':r'\}','_':r'\_',
                 '&':r'\&','%':r'\%','#':r'\#','$':r'\$',
                 '^':r'\textasciicircum{}','~':r'\textasciitilde{}'}
        tex_author=''.join(escapes.get(ch,ch)for ch in author)
        tex=tex.replace(r'\author{}',r'\author{'+tex_author+'}')
        tex=tex.replace('No Lean verification or external peer review is claimed.',
            'The accompanying formalization passed the recorded Lean 4.19.0 build and audit. '
            'Independent human peer review is not claimed.')
        tex=tex.replace(r'\end{document}',
            r'\paragraph{Assistance.} Substantial OpenAI ChatGPT/Codex assistance was used '
            'in the proof, writing, formalization, and debugging.\n'+r'\end{document}')
        out['paper/PROOF.tex']=tex.encode()
        out['experiments/verify_A220119.py']=archive.read('written_proof/verify_A220119.py')
        out['evidence/finite_checks.json']=archive.read('written_proof/verification.json')
        historical=archive.read('written_proof/status_and_sources.md')
        out['evidence/prior_art_search.md']=(
            b'Historical search notes; build status in these notes predates formal verification.\n'
            b'See colab_status.json for the recorded successful build.\n\n'+historical)
        out['OEIS_SUBMISSION_GUIDE.md']=asset('OEIS_SUBMISSION_GUIDE.md')
        out['ci_verify.py']=asset('ci_verify.py')
        out['tools/publish_github.py']=asset('publish_github.py')
        out['tools/GITHUB_PUBLICATION_CELL.py']=asset('GITHUB_PUBLICATION_CELL.py')
        notebook=json.loads(asset('A220119_Lean_Colab.ipynb'))
    runner=(source/'compile_in_lake.py').read_bytes()
    runner_hash=hashlib.sha256(runner).hexdigest()
    # Rebuild the notebook's upload check for the ACTUAL runner that passed.
    code=''.join(notebook['cells'][1]['source'])
    code,count=re.subn(r"(?m)^expected_runner = '[0-9a-f]{64}'$",
                       'expected_runner = '+repr(runner_hash),code)
    if count!=1:raise RuntimeError('Unexpected notebook format; no repository created.')
    notebook['cells'][1]['source']=code.splitlines(True)
    notebook_bytes=(json.dumps(notebook,indent=1)+'\n').encode()
    out['notebooks/A220119_Lean_Colab.ipynb']=notebook_bytes
    for name,data in modules.items():out['source/'+name]=data
    out['source/compile_in_lake.py']=runner
    out['source/lean-toolchain']=b'leanprover/lean4:v4.19.0\n'
    manifest={name:hashlib.sha256(data).hexdigest()for name,data in modules.items()}
    out['source/source_manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    standalone=['import Mathlib\n\n/-! Convenience concatenation of checked modules.\n'
                'The authoritative verification is the recorded multi-module build. -/\n']
    for name in ORDER:
        standalone.append('\n/- '+name+' -/\n')
        standalone.append('\n'.join(line for line in modules[name].decode().splitlines()
                                     if not line.startswith('import '))+'\n')
    out['source/A220119_Standalone.lean']=''.join(standalone).encode()
    out['source/README.md']=b'Use the repository README and recorded verification evidence.\n'
    out['evidence/colab_status.json']=(json.dumps(status,indent=2)+'\n').encode()
    for name in ['lean_version.log','import_smoke.log','axiom_audit.log']+[
            name.replace('/','_')+'.log'for name in ORDER]:
        out['evidence/colab_logs/'+name]=(source/'logs'/name).read_bytes()
    env_path=base/'environment.json'
    environment=json.loads(env_path.read_text())if env_path.exists()else{}
    mathlib=base/'mathlib-v4.19.0'
    commit=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
    if environment.get('mathlib_commit',commit)!=commit:
        raise RuntimeError('Dependency checkout changed since setup; no repository created.')
    if not re.fullmatch(r'[0-9a-f]{40}',commit):raise RuntimeError('Invalid mathlib revision')
    environment.update(mathlib_commit=commit,toolchain='leanprover/lean4:v4.19.0')
    out['evidence/environment.json']=(json.dumps(environment,indent=2)+'\n').encode()
    out['.gitignore']=b'*.olean\n*.ilean\n.lake/\n__pycache__/\nsource/logs/\nsource/status.json\nsource/ImportSmoke.lean\n'
    out['.github/workflows/lean.yml']=b'''name: Lean proof check
on: [push, workflow_dispatch]
permissions:
  contents: read
jobs:
  verify:
    runs-on: ubuntu-latest
    timeout-minutes: 60
    steps:
      - name: Fetch this exact revision
        run: |
          git init .
          git remote add origin "https://github.com/${GITHUB_REPOSITORY}.git"
          git fetch --depth=1 origin "${GITHUB_SHA}"
          git checkout --detach FETCH_HEAD
      - name: Reproduce the Lean build and axiom audit
        run: python3 ci_verify.py
'''
    out['README.md']=f'''# A220119 constant-term identity

Human contributor and submitter: {author}.

This repository proves the constant-term identity attributed to F. Chapoton
(25 May 2026) in [OEIS A220119](https://oeis.org/A220119), for every n >= 0.
The sequence's separate (n+1)(n+2) divisibility conjecture is outside this result.

- [Written algebraic proof](paper/PROOF.md), with [LaTeX source](paper/PROOF.tex).
- [Exact original-statement audit](source/Audit.lean).
- [Universal Lean theorem](source/A220119/Main.lean).
- [Successful Colab build record](evidence/colab_status.json) and [axiom audit](evidence/colab_logs/axiom_audit.log).

## Verification

The six Lean modules in source/ are the actual files hashed in the successful Colab run.
All six modules compiled with Lean 4.19.0; the separate original-statement audit
passed. Only propext, Classical.choice, and Quot.sound are permitted by the audit.
This is ordinary Lean kernel verification, not a second independent kernel.
The concatenated standalone file is a convenience copy and was not separately checked.
Numerical checks are supporting evidence, separate from the universal theorem.

To reproduce in Colab, open notebooks/A220119_Lean_Colab.ipynb and upload the
complete assets/A220119_Lean_Colab.zip when the first cell asks. A High-RAM CPU
runtime gives headroom; no GPU is needed. The exact minimum RAM is unmeasured.

To reproduce locally or on the configured GitHub Actions runner:

    python3 ci_verify.py

That script fetches the recorded mathlib commit and Lean version. The Actions
result is separate from the saved Colab evidence; its success is not assumed.

## Provenance and scope

Substantial OpenAI ChatGPT/Codex assistance was used in proof discovery,
drafting, formalization, and debugging. The human contributor is responsible
for the submission. No independent human mathematical review is claimed here.
The defining double sum predates this work (Almkvist and Zudilin, 2004).
The conjectured Laurent polynomial is credited to Chapoton, not claimed as a
new discovery. A targeted prior-art search did not find an earlier proof;
first priority has not been established.

For OEIS submission, see OEIS_SUBMISSION_GUIDE.md. That file is a factual
checklist; write your own comment in accordance with OEIS's AI guidance.
'''.encode()
    # The complete upload bundle is rebuilt from checked runtime files.
    stream=io.BytesIO()
    with zipfile.ZipFile(stream,'w',zipfile.ZIP_DEFLATED)as archive:
        for name,data in out.items():
            if name.startswith('source/'):
                archive.writestr('A220119_Lean/'+name[len('source/'):],data)
        archive.writestr('A220119_Lean/A220119_Lean_Colab.ipynb',notebook_bytes)
        for name in ['OEIS_SUBMISSION_GUIDE.md','ci_verify.py','tools/publish_github.py',
                     'tools/GITHUB_PUBLICATION_CELL.py']:
            archive.writestr('A220119_Lean/'+Path(name).name,out[name])
        for dst,src in [('A220119_proof.md','paper/PROOF.md'),('A220119_proof.tex','paper/PROOF.tex'),
                        ('verify_A220119.py','experiments/verify_A220119.py'),
                        ('verification.json','evidence/finite_checks.json'),
                        ('status_and_sources.md','evidence/prior_art_search.md')]:
            archive.writestr('written_proof/'+dst,out[src])
    out['assets/A220119_Lean_Colab.zip']=stream.getvalue()
    hashes={name:hashlib.sha256(data).hexdigest()for name,data in out.items()}
    out['FILE_SHA256.json']=(json.dumps(hashes,indent=2)+'\n').encode()
    return out

def publish(base,asset_bytes):
    checked_sources(base)  # Before asking for credentials or creating anything.
    author=input('Public author name: ').strip()
    if not author:raise ValueError('A contributor name is required')
    files=package(base,asset_bytes,author)
    destination=base/'github_ready'
    destination.mkdir(exist_ok=True)
    for name,data in files.items():
        target=destination/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    print('Prepared',len(files),'publication files at',destination)
    name=input('New PUBLIC repo name [oeis-a220119-constant-term]: ').strip()or'oeis-a220119-constant-term'
    if not re.fullmatch(r'[A-Za-z0-9_.-]{1,100}',name):raise ValueError('Invalid repository name')
    print('Use a GitHub classic PAT with public_repo and workflow scopes, or equivalent fine-grained permissions.')
    token=getpass.getpass('GitHub token (hidden; never saved): ').strip()
    if not token:raise ValueError('No token supplied')
    def api(method,path,payload=None,missing_ok=False):
        body=None if payload is None else json.dumps(payload).encode()
        req=request.Request('https://api.github.com'+path,data=body,method=method,headers={
            'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json',
            'X-GitHub-Api-Version':'2026-03-10','Content-Type':'application/json',
            'User-Agent':'A220119-proof-publication'})
        for attempt in range(4):
            try:
                with request.urlopen(req,timeout=90)as response:return json.load(response)
            except error.HTTPError as problem:
                if missing_ok and problem.code==404:return None
                if method=='GET'and problem.code in {404,409,502,503}and attempt<3:
                    time.sleep(attempt+1)
                    continue
                try:message=json.loads(problem.read()).get('message','Request failed')
                except Exception:message='Request failed'
                raise RuntimeError(f'GitHub {method} {path}: {problem.code}: {message}')from None
    user=api('GET','/user');owner=user['login'];prefix=f'/repos/{owner}/{name}'
    if api('GET',prefix,missing_ok=True)is not None:
        raise RuntimeError('That repository already exists; choose a new name. Existing repositories are not modified.')
    repo=api('POST','/user/repos',{'name':name,'private':False,'auto_init':True,
        'description':'Proof and Lean formalization of the constant-term identity in OEIS A220119'})
    print('Created public repository:',repo['html_url'])
    branch=repo['default_branch'];ref=api('GET',prefix+'/git/ref/heads/'+parse.quote(branch,safe=''))
    head=ref['object']['sha'];parent=api('GET',prefix+'/git/commits/'+head)
    entries=[]
    for filename,data in sorted(files.items()):
        entry={'path':filename,'mode':'100644','type':'blob'}
        try:entry['content']=data.decode('utf-8')
        except UnicodeDecodeError:
            blob=api('POST',prefix+'/git/blobs',{'content':base64.b64encode(data).decode(),'encoding':'base64'})
            entry['sha']=blob['sha']
        entries.append(entry)
    tree=api('POST',prefix+'/git/trees',{'base_tree':parent['tree']['sha'],'tree':entries})
    commit=api('POST',prefix+'/git/commits',{
        'message':'Publish A220119 proof and recorded Lean verification',
        'tree':tree['sha'],'parents':[head],
        'author':{'name':author,'email':f"{user['id']}+{owner}@users.noreply.github.com"}})
    api('PATCH',prefix+'/git/refs/heads/'+parse.quote(branch,safe=''),{'sha':commit['sha'],'force':False})
    sha=commit['sha'];url=repo['html_url'];proof_url=f'{url}/blob/{sha}/paper/PROOF.md'
    result={'repository':url,'commit':sha,'proof':proof_url,
            'formalization':f'{url}/tree/{sha}/source','actions':url+'/actions'}
    (base/'github_publication.json').write_text(json.dumps(result,indent=2)+'\n')
    links=(f'{html.escape(author)}, <a href="{proof_url}">A proof of the constant-term identity in A220119</a>, 2026.\n'
           f'{html.escape(author)}, <a href="{url}/tree/{sha}">Lean formalization, verification logs, and reproducible source</a>.\n')
    (base/'OEIS_LINKS.txt').write_text(links)
    print('\nPUBLISHED:',url,'\nCOMMIT:',sha,'\nPROOF:',proof_url,'\nACTIONS:',url+'/actions')
    print('\nLinks-field metadata (write your own OEIS comment):\n'+links)
    print('Saved publication details:',base/'github_publication.json')
    token=''
    return result

if __name__=='__main__':
    if 'ASSET_BYTES'not in globals():
        raise RuntimeError('Run the supplied Colab publication cell and upload the entire updated asset ZIP.')
    publish(Path('/content/A220119_Lean'),ASSET_BYTES)
