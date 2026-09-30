#!/usr/bin/env python3
"""Verify the selective source manifest, then compile in dependency order (at most two jobs).
Default: rebuild all project modules into a separate output directory.
--cached: reuse available project oleans; always compile Certificate.lean afresh.
Mathlib and its pinned dependencies must already be available: `lake exe cache get`.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time

ROOT=Path(__file__).resolve().parents[1]
NAMESPACES=['BouRabeeGwynne','ReflectedWalk','ReflectedGMS','QuantumZipper','LQGDimension']
def stripped(s):
    res=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-':depth+=1;i+=2
            elif s[i:i+2]=='-/':depth-=1;i+=2
            else:res.append('\n' if s[i]=='\n' else ' ');i+=1
        elif not string and s[i:i+2]=='/-':depth=1;i+=2
        elif not string and s[i:i+2]=='--':
            end=s.find('\n',i);i=len(s) if end<0 else end
        elif s[i]=='"':string=not string;res.append(' ');i+=1
        elif string and s[i]=='\\':i+=2
        else:res.append(' ' if string else s[i]);i+=1
    return ''.join(res)
def imports(s):
    return [m for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',stripped(s),re.M) for m in line.split() if m!='all']
def scan(manifest):
    modules=manifest['modules']; names=set(modules)
    present={str(p.relative_to(ROOT)) for ns in NAMESPACES for p in (ROOT/ns).rglob('*') if p.is_file()}
    assert present=={r['path'] for r in modules.values()},'Unexpected or missing proof files'
    for mod,row in modules.items():
        assert row['path']==str(Path(*mod.split('.')).with_suffix('.lean')),f'Module path mismatch: {mod}'
        assert re.fullmatch(r'[0-9a-f]{40}',row.get('source_commit',manifest['source_commit'])),f'Invalid source provenance: {mod}'
        data=(ROOT/row['path']).read_bytes()
        assert len(data)==row['bytes'],f'Source size mismatch: {mod}'
        assert hashlib.sha256(data).hexdigest()==row['sha256'],f'Source hash mismatch: {mod}'
        text=data.decode();actual=imports(text)
        assert actual==row['imports'],f'Import mismatch: {mod}'
        assert [d for d in actual if d.split('.')[0] in NAMESPACES]==row['local_imports'],f'Local import classification mismatch: {mod}'
        bad=re.findall(r'\b(?:sorry|admit|axiom|sorryAx|implemented_by)\b|debug\.skipKernelTC|\bunsafe\s+(?:def|theorem)\b',stripped(text))
        assert not bad,f'Forbidden proof token in {mod}: {bad}'
        assert all(d in names for d in row['local_imports']),f'Missing local import: {mod}'
    closure=set();pending=list(manifest['roots'])
    while pending:
        m=pending.pop()
        if m not in closure:closure.add(m);pending.extend(modules[m]['local_imports'])
    assert closure==names,'Manifest contains modules outside the selected import closure'
    for p in ROOT.rglob('*'):
        rel=p.relative_to(ROOT)
        if rel.parts[0] in ['.git','.lake']:continue
        assert not p.is_symlink(),f'Unexpected public symlink: {rel}'
        assert rel.parts[0] not in ['work','work_orders','outputs','manuscripts','paper'],f'Private directory: {rel}'
    print(f'Source scan passed: {len(modules)} byte-preserved modules, exact import closure.',flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cached',action='store_true');ap.add_argument('--scan-only',action='store_true');ap.add_argument('--jobs',type=int,default=2,choices=[1,2]);args=ap.parse_args()
    manifest=json.loads((ROOT/'source-manifest.json').read_text());scan(manifest)
    if args.scan_only:return
    lean=subprocess.check_output(['elan','which','lean'],cwd=ROOT,text=True).strip()
    out=ROOT/'.lake/verification';lib=out/'lib/lean';logs=out/'logs';lib.mkdir(parents=True,exist_ok=True);logs.mkdir(parents=True,exist_ok=True)
    packages=ROOT/'.lake/packages'
    assert packages.is_dir(),'Run lake exe cache get first'
    paths=[lib]
    cache=ROOT/'.lake/build/lib/lean'
    if args.cached:paths.append(cache)
    paths += sorted(p/'.lake/build/lib/lean' for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir())
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
    modules=dict(manifest['modules']);done=set();running={};fresh=[];reused=[];start=time.time()
    if args.cached:
        for m,row in modules.items():
            rel=Path(row['path']).with_suffix('.olean')
            if (cache/rel).exists():done.add(m);reused.append(m)
    print(f'Build: {len(modules)-len(done)} project modules pending, {len(reused)} cached; max {args.jobs} compilers.',flush=True)
    def launch(mod,path):
        dest=lib/Path(path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        fh=(logs/(mod+'.log')).open('w')
        p=subprocess.Popen([lean,'-j1','-M8192',path,'-o',str(dest)],cwd=ROOT,env=env,stdout=fh,stderr=subprocess.STDOUT)
        return p,fh,time.time()
    try:
        while len(done)<len(modules):
            for m,(p,fh,t) in list(running.items()):
                rc=p.poll()
                if rc is None:
                    if time.time()-t>900:raise RuntimeError(f'Module timed out after 900 seconds: {m}')
                    continue
                fh.close();del running[m]
                if rc:raise RuntimeError(f'Compile failed: {m}\n'+(logs/(m+'.log')).read_text()[-12000:])
                done.add(m);fresh.append(m)
                print(f'[{len(done)}/{len(modules)}] {m} ({time.time()-t:.1f}s)',flush=True)
            for m,row in modules.items():
                if len(running)>=args.jobs:break
                if m not in done and m not in running and all(d in done for d in row['local_imports']):running[m]=launch(m,row['path'])
            if not running and len(done)<len(modules):raise RuntimeError('No ready module: invalid dependency graph')
            time.sleep(.25)
        p,fh,t=launch('Certificate','Certificate.lean');rc=p.wait(timeout=900);fh.close()
        certificate=(logs/'Certificate.log').read_text();print(certificate,flush=True)
        if rc:raise RuntimeError('Certificate failed')
        assert 'PUBLIC_RELEASE_AUDIT' in certificate,'Whole-declaration audit did not finish'
        source_commits=sorted({r.get('source_commit',manifest['source_commit']) for r in modules.values()})
        result={'status':'passed','mode':'cached dependencies with freshly compiled certificate' if args.cached else 'fresh project source rebuild and certificate','source_commits':source_commits,'source_modules':len(modules),'fresh_modules':len(fresh),'reused_modules':len(reused),'seconds':round(time.time()-start,1),'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),'axioms_allowed':['propext','Classical.choice','Quot.sound']}
        (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
    finally:
        for p,fh,t in running.values():
            if p.poll() is None:p.terminate()
            fh.close()
if __name__=='__main__':main()
