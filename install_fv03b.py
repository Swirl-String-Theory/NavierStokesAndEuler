"""Safe add-only install; default dry run. Existing v0.1.0 sources untouched."""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys

BASE=Path(__file__).resolve().parent
BRANCH='sst/formal-euler-feedback-v0.2.0'
FILES=[
  'SSTFormal/EulerFeedback/PDEtoODE.lean',
  'SSTFormal/EulerFeedback/PressureHessian.lean',
  'SSTFormal/EulerFeedback/FlowCoverage.lean',
  'SSTFormal/EulerFeedback/VALIDATION_FV03B_STARTER.json',
  'tools/run_fv03b.py',
  'tools/make_app07_fv03b_contract.py',
  'run_sstformal_eulerfeedback_v0.2.0.cmd',
  'tests/test_fv03b.py',
  'README_FV03B_v0.2.0.md',
  'examples/README.md',
]

def main(argv=None):
  ap=argparse.ArgumentParser()
  ap.add_argument('--repo',required=True,type=Path)
  ap.add_argument('--apply',action='store_true')
  a=ap.parse_args(argv)
  root=a.repo.expanduser().resolve()
  if not (root/'lakefile.toml').is_file() or not (root/'.git').exists():
    print('REFUSED_NOT_LEAN_REPO:',root);return 2
  p=subprocess.run(['git','-C',str(root),'branch','--show-current'],capture_output=True,text=True)
  if p.returncode or p.stdout.strip()!=BRANCH:
    print('REFUSED_BRANCH: expected',BRANCH,'got',p.stdout.strip());return 2
  for f in ['StretchingBound.lean','VorticityBound.lean','EulerianTransfer.lean']:
    if not (root/'SSTFormal'/'EulerFeedback'/f).is_file():
      print('REFUSED_MISSING_FV03A_SOURCE:',f);return 2
  conflict=[];new=[];identical=[]
  for name in FILES:
    src=BASE/name;dst=root/name
    if not src.is_file():print('PACKAGING_ERROR:',name);return 4
    if dst.exists():
      if dst.is_file() and hashlib.sha256(src.read_bytes()).digest()==hashlib.sha256(dst.read_bytes()).digest():
        identical.append(name)
      else:conflict.append(name)
    else:new.append(name)
  if conflict:
    print('REFUSED_EXISTING_FILES_DIFFER:',*conflict,sep='\n');return 3
  print('NEW:',*new,sep='\n');print('IDENTICAL:',*identical,sep='\n')
  if a.apply:
    for name in new:
      src=BASE/name;dst=root/name;dst.parent.mkdir(parents=True,exist_ok=True)
      with dst.open('xb') as out,src.open('rb') as inp:shutil.copyfileobj(inp,out)
    print('INSTALL_COMPLETE; prior proofs unchanged')
  else:print('DRY_RUN; use --apply')
  return 0

if __name__=='__main__':sys.exit(main())
