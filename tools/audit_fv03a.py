"""Strict local post-build axiom audit for SST-FV03-A.

No Lean execution is performed here: the .cmd script has already invoked Lean.
The audit checks the captured #print axioms lines and source hashes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEOREMS = [
    'weightedInvariant_hasDerivAt_zero',
    'weightedInvariant_constant_before_endpoint',
    'scalar_stretching_identity',
    'scalar_stretching_upper_bound',
    'uniform_material_stretching_bound',
    'skew_operator_has_zero_aligned_stretch',
    'aligned_stretch_ignores_skew_part',
    'vorticity_norm_sq_hasDerivAt',
    'vorticity_norm_sq_scalar_law',
    'vorticity_norm_sq_bound_before_endpoint',
    'vorticity_norm_bound_before_endpoint',
    'eulerian_norm_sq_bound_from_trajectory_coverage',
    'eulerian_norm_bound_from_trajectory_coverage',
]
ALLOWED = {'propext','Classical.choice','Quot.sound'}
PATTERN = re.compile(r"['\"]?(SSTFormal\.EulerFeedback\.[A-Za-z0-9_]+)['\"]?\s+depends on axioms:\s*\[([^\]]*)\]")
NO_AXIOMS = re.compile(r"['\"]?(SSTFormal\.EulerFeedback\.[A-Za-z0-9_]+)['\"]?\s+does not depend on any axioms")
SOURCE_FILES = [
    'SSTFormal/EulerFeedback/StretchingBound.lean',
    'SSTFormal/EulerFeedback/VorticityBound.lean',
    'SSTFormal/EulerFeedback/EulerianTransfer.lean',
]

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def git(*args: str) -> str | None:
    p=subprocess.run(['git', '-C', str(ROOT), *args],capture_output=True,text=True,check=False)
    return p.stdout.strip() if p.returncode == 0 else None

def audit(text: str):
    found={}
    errors=[]
    for name, values in PATTERN.findall(text):
        if name in found:
            errors.append('DUPLICATE_AXIOM_AUDIT: '+name)
        found[name]={p.strip() for p in values.split(',') if p.strip()}
    for name in NO_AXIOMS.findall(text):
        if name in found: errors.append('DUPLICATE_AXIOM_AUDIT: '+name)
        found[name]=set()
    expected={'SSTFormal.EulerFeedback.'+x for x in THEOREMS}
    for name in sorted(expected-set(found)):
        errors.append('MISSING_PRINT_AXIOMS: '+name)
    for name in sorted(set(found)-expected):
        errors.append('UNEXPECTED_THEOREM: '+name)
    for name,v in found.items():
        if not v.issubset(ALLOWED):
            errors.append('DISALLOWED_AXIOMS: '+name+': '+', '.join(sorted(v-ALLOWED)))
    if re.search(r'\bsorryAx\b',text):
        errors.append('SORRY_AX_IN_BUILD_OUTPUT')
    if re.search(r'(?im)^\s*(?:error:|.*\.lean:\d+:\d+: error:)',text):
        errors.append('LEAN_ERROR_IN_BUILD_OUTPUT')
    return found,errors

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--log',required=True)
    ap.add_argument('--out',required=True)
    ns=ap.parse_args()
    log=(ROOT/ns.log).resolve()
    outfile=(ROOT/ns.out).resolve()
    if outfile.exists():
        raise SystemExit('REFUSE_OVERWRITE: '+str(outfile))
    text=log.read_text(encoding='utf-8',errors='replace')
    found,errors=audit(text)
    branch=git('branch','--show-current')
    commit=git('rev-parse','HEAD')
    if not branch or not commit:
        errors.append('GIT_REPOSITORY_NOT_VERIFIED')
    expected_branch='sst/formal-euler-feedback-v0.1.0'
    if branch and branch!=expected_branch:
        errors.append('UNEXPECTED_GIT_BRANCH: '+branch)
    # POSIX keys so Windows backslashes do not break downstream contract matching.
    source_hashes={p.as_posix():sha(ROOT/p) for p in map(Path,SOURCE_FILES)}
    result={
      'id':'SST-FV03A','version':'v0.1.0',
      'stage':'A-conditional-euler-stretching-bound',
      'status':'PASS_LOCAL_LEAN' if not errors else 'FAIL',
      'lean_exit_code':0 if not errors else None,
      'execution':{'executed_by':'user_local','independent_assistant_execution':False,
                   'comparator_executed':False,'gpu_backend_executed':False},
      'toolchain_expected':'leanprover/lean4:v4.34.0-rc2',
      'git':{'branch':branch,'commit':commit,'expected_branch':expected_branch},
      'allowed_axioms':sorted(ALLOWED),
      'theorems':{k:sorted(v) for k,v in sorted(found.items())},
      'theorem_count_expected':len(THEOREMS),
      'theorem_count_checked':len(found),
      'no_sorryAx_reported':not bool(re.search(r'\bsorryAx\b',text)),
      'evidence':{'build_log':str(log),'build_log_sha256':sha(log), 'source_sha256':source_hashes},
      'errors':errors,
      'scientific_status':'UNRESOLVED',
      'scope':'Conditional ODE/PDE-bridge prerequisites; no proof that a free Ruban trefoil or any Euler solution meets the integrated stretching cap.',
      'open_gates':['G3 pressure-Hessian closure','G4 actual Euler trajectory bridge',
                    'G5 global coverage/incompressibility','G6 independent verification',
                    'G7 Ruban/numerical CPU and GPU validation'],
    }
    outfile.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+'\n',encoding='utf-8')
    print('[{}] FV03A audit: {} / {} theorem records; {}'.format(result['status'],len(found),len(THEOREMS),', '.join(errors) if errors else 'only permitted axioms'))
    return 0 if not errors else 2

if __name__=='__main__':
    sys.exit(main())
