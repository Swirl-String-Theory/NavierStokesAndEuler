"""FV03-B1 -> B2 -> B3 strict sequential Lean verifier.

No result is PASS unless that exact stage's Lean process exits 0, an .olean
was created, every declared #print axioms result is present and permitted,
and no Lean error or sorryAx was observed. On failure, successors are BLOCKED.
"""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_BRANCH = 'sst/formal-euler-feedback-v0.2.0'
PARENT_SHA = '357fd80'
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
MODULES = (
    ('B1', 'PDEtoODE', (
        'euler_momentum_implies_curl_balance',
        'euler_momentum_implies_material_curl_rhs',
        'material_chain_rule_to_linear_ode',
        'smooth_euler_material_vorticity_ode')),
    ('B2', 'PressureHessian', (
        'gradient_riccati_rhs_norm_le',
        'pressure_hessian_balance_at_time',
        'material_gradient_derivative_norm_le',
        'riccati_strain_rotation_decomposition',
        'pressure_strain_alignment_of_skew_decomposition')),
    ('B3', 'FlowCoverage', (
        'finite_horizon_material_flow_covers_space',
        'finite_horizon_material_bound_implies_eulerian_bound')),
)
SOURCE_DIR = Path('SSTFormal/EulerFeedback')
PRIOR = ('StretchingBound.lean','VorticityBound.lean','EulerianTransfer.lean')
AXIOM_LINE = re.compile(
    r"['\"]?(SSTFormal\.EulerFeedback\.[A-Za-z0-9_]+)['\"]?\s+depends on axioms:\s*\[([^\]]*)\]")
ZERO_LINE = re.compile(r"['\"]?(SSTFormal\.EulerFeedback\.[A-Za-z0-9_]+)['\"]?\s+does not depend on any axioms")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str):
    try:
        p = subprocess.run(['git', '-C', str(ROOT), *args], capture_output=True, text=True)
    except OSError:
        return None
    return p.stdout.strip() if p.returncode == 0 else None


def preflight() -> list[str]:
    errors=[]
    if not (ROOT/'lakefile.toml').is_file():
        errors.append('REPOSITORY_LAKEFILE_MISSING')
    tc=ROOT/'lean-toolchain'
    if not tc.is_file() or tc.read_text(encoding='utf-8').strip()!='leanprover/lean4:v4.34.0-rc2':
        errors.append('LEAN_TOOLCHAIN_MISMATCH_OR_MISSING')
    branch=git('branch','--show-current')
    if branch != EXPECTED_BRANCH:
        errors.append(f'BRANCH_MISMATCH: got {branch!r}; expected {EXPECTED_BRANCH}')
    if not git('rev-parse','HEAD'):
        errors.append('GIT_COMMIT_NOT_AVAILABLE')
    try:
        anc=subprocess.run(['git','-C',str(ROOT),'merge-base','--is-ancestor',PARENT_SHA,'HEAD'],capture_output=True)
        if anc.returncode!=0:errors.append('PARENT_FV03A_COMMIT_NOT_ANCESTOR: '+PARENT_SHA)
    except OSError:
        errors.append('GIT_PARENT_CHECK_NOT_AVAILABLE')
    if not shutil.which('lake'):
        errors.append('LAKE_TOOLCHAIN_NOT_FOUND')
    for f in PRIOR:
        if not (ROOT/SOURCE_DIR/f).is_file():
            errors.append('FV03A_PREREQUISITE_MISSING: '+f)
    for _,name,_ in MODULES:
        p=ROOT/SOURCE_DIR/(name+'.lean')
        if not p.is_file():
            errors.append('FV03B_SOURCE_MISSING: '+str(p))
        else:
            if re.search(r'\b(?:sorry|admit|sorryAx)\b|^\s*(?:axiom|constant)\b',
                         re.sub(r'/\-.*?\-/', '', p.read_text(encoding='utf-8'),flags=re.S),
                         flags=re.M):
                errors.append('UNSAFE_PROOF_PLACEHOLDER: '+name)
    return errors


def parse_axioms(log: str, expected: tuple[str,...]):
    """Strictly verify EXACT audit targets; never infer success from .olean alone."""
    found={}
    errors=[]
    for full,s in AXIOM_LINE.findall(log):
        if full in found: errors.append('DUPLICATE_AXIOM_RECORD: '+full)
        found[full]=[x.strip() for x in s.split(',') if x.strip()]
    for full in ZERO_LINE.findall(log):
        if full in found: errors.append('DUPLICATE_AXIOM_RECORD: '+full)
        found[full]=[]
    exp={'SSTFormal.EulerFeedback.'+x for x in expected}
    for full in sorted(exp-set(found)):
        errors.append('MISSING_AXIOM_RECORD: '+full)
    for full in sorted(set(found)-exp):
        errors.append('UNEXPECTED_AXIOM_RECORD: '+full)
    for full,axs in found.items():
        if not set(axs).issubset(AXIOMS):
            errors.append('DISALLOWED_AXIOM: '+full+': '+','.join(sorted(set(axs)-AXIOMS)))
    if re.search(r'\bsorryAx\b',log): errors.append('SORRYAX_IN_LOG')
    if re.search(r'(?mi)^\s*(?:error:|.*\.lean:\d+:\d+: error:)',log):
        errors.append('LEAN_ERROR_IN_LOG')
    return found,errors


def report_stages(stages):
    by={x['id']:x['status'] for x in stages}
    def gate(id, stage, question, why):
        status=by[stage]
        return {'id':id,'status':'PASS' if status=='PASS_LOCAL_LEAN' else
                ('BLOCKED' if status=='BLOCKED' else 'NOT_EXECUTED' if status=='NOT_EXECUTED' else 'FAIL'),
                'question':question,'stage':stage,'justification':why}
    gs=[
        gate('GB1_FORMAL_PDE_CHAIN','B1','Does the local smooth-Euler curl/momentum calculus imply the material vorticity ODE?',
             'Euler momentum and divergence plus explicit curl-time and joint regularity hypotheses.'),
        gate('GB2_RICCATI_IDENTITY','B2','Are pressure-Hessian Riccati algebra and norm estimates formalized?',
             'Riccati gradient-law remains an explicitly named premise for the derivative theorem.'),
        gate('GB3_FINITE_FLOW_COVERAGE','B3','Is material-flow coverage constructed at each finite regular horizon?',
             'Constructed inverse from Euler.FiniteIntervalFlow; bounded-Lipschitz finite-horizon hypotheses.'),
        {'id':'G2_ACTUAL_EULER_INSTANTIATION','status':'UNRESOLVED',
          'question':'Are the curl-time and joint differentiability prerequisites discharged for the particular maximal Euler field?',
          'justification':'No dedicated instantiation of Euler.Solution maximal fields in this version.'},
        {'id':'G3_NONCIRCULAR_STRETCHING_CAP','status':'UNRESOLVED',
          'question':'Does pressure-Hessian feedback imply the uniform accumulated stretching cap without assuming regularity?',
          'justification':'No sign/coercivity estimate deduced; pressure-Hessian is not intrinsically stabilizing.'},
        {'id':'G4_MAXIMAL_FLOW_COVERAGE','status':'UNRESOLVED',
          'question':'Is finite-horizon flow coverage instantiated for every S<T* in the particular Euler solution?',
          'justification':'B3 constructs flows given bounded Lipschitz finite-horizon velocity; no Euler.Solution instantiation.'},
        {'id':'G5_RUBAN','status':'NOT_EXECUTED','question':'Is a Ruban Trefoil shown to satisfy the cap?',
          'justification':'No Ruban finite-core field or trajectory simulation in formal proof stage.'},
        {'id':'G6_CPU_GPU','status':'NOT_EXECUTED','question':'Did independent reference and Arc/CUDA numerical lanes execute?',
          'justification':'This release contains Lean proof and Python orchestration tests only.'},
        {'id':'G7_INDEPENDENT_LEAN','status':'NOT_EXECUTED','question':'Was an independent second-kernel/formal rerun performed?',
          'justification':'Local Lean compile is separate from independent Comparator and CI.'}
    ]
    return gs


def run(output: Path, dry_run=False):
    if output.exists():
        raise ValueError('OUTPUT_ALREADY_EXISTS: '+str(output))
    output.mkdir(parents=True)
    errors=preflight()
    stages=[]
    source_paths=[ROOT/SOURCE_DIR/(name+'.lean') for _,name,_ in MODULES]
    for code,name,targets in MODULES:
        src=ROOT/SOURCE_DIR/(name+'.lean')
        stages.append({'id':code,'module':'SSTFormal.EulerFeedback.'+name,
                       'source':str(src),'source_sha256':digest(src) if src.is_file() else None,
                       'expected_theorems':list(targets),'theorem_count':len(targets),
                       'status':'NOT_EXECUTED','lean_exit_code':None,'axioms':{},'errors':[],
                       'log_file':None,'log_sha256':None,'olean_sha256':None})
    if dry_run:
        global_errors=errors
        state='DRY_RUN_ONLY'
    elif errors:
        global_errors=errors
        state='BLOCKED'
        for st in stages: st['status']='BLOCKED';st['errors']=errors
    else:
        global_errors=[]
        for i,(code,name,targets) in enumerate(MODULES):
            st=stages[i]
            ole=ROOT/'.lake'/'build'/'lib'/'lean'/'SSTFormal'/'EulerFeedback'/(name+'.olean')
            ole.parent.mkdir(parents=True,exist_ok=True)
            # Remove any stale .olean to make a zero-exit result unambiguous.
            if ole.exists(): ole.unlink()
            log=output/(code+'_'+name+'.log')
            args=['lake','env','lean','-o',str(ole.relative_to(ROOT)),
                  str((SOURCE_DIR/(name+'.lean')).as_posix())]
            try:
                proc=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,encoding='utf-8',errors='replace')
                body=proc.stdout
                rc=proc.returncode
            except OSError as e:
                body='FAILED_TO_LAUNCH_LEAN: '+str(e)+'\n'
                rc=127
            log.write_text('CMD: '+' '.join(args)+'\n\n'+body,encoding='utf-8')
            found,issues=parse_axioms(body,targets)
            if rc!=0:issues.append('LEAN_EXIT_CODE: '+str(rc))
            if not ole.is_file():issues.append('LEAN_OLEAN_MISSING')
            st.update({'lean_exit_code':rc,'axioms':found,'errors':issues,
                       'log_file':str(log),'log_sha256':digest(log),
                       'olean_sha256':digest(ole) if ole.is_file() else None,
                       'status':'PASS_LOCAL_LEAN' if not issues else 'FAIL'})
            if issues:
                state='FAIL'
                for future in stages[i+1:]:
                    future['status']='BLOCKED'
                    future['errors']=['BLOCKED_BY_'+code]
                break
        else:
            state='PASS_LOCAL_LEAN'
    checks={'stage_order':[s['id'] for s in stages],
            'all_stages_local_pass':all(s['status']=='PASS_LOCAL_LEAN' for s in stages),
            'new_axioms_absent_in_lean_log':all(s['status']=='PASS_LOCAL_LEAN' for s in stages),
            'independent_assistant_execution':False,
            'gpu_backend_executed':False,
            'physical_stabilization_certified':False}
    result={'id':'SST-FV03B','version':'v0.2.0','stage':'B1-B2-B3-sequential',
            'status':state,'scientific_status':'UNRESOLVED',
            'git':{'branch':git('branch','--show-current'),
                   'commit':git('rev-parse','HEAD'),
                   'base_commit_expected_ancestor':PARENT_SHA},
            'toolchain_expected':'leanprover/lean4:v4.34.0-rc2',
            'allowed_axioms':sorted(AXIOMS),
            'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in source_paths if p.is_file()},
            'stages':stages,'gates':report_stages(stages),'checks':checks,
            'preflight_errors':global_errors,
            'notes':['B1 proves PDE-to-material ODE assuming explicit regularity identities, not instantiation to Euler.Solution.',
                     'B2 formalizes Riccati identity/estimates; no automatic stretching cap.',
                     'B3 constructs finite-horizon coverage for bounded Lipschitz velocities; no uniform endpoint extension.',
                     'Formal Lean PASS is not a numerical, GPU or physics certification.']}
    (output/'VALIDATION_FV03B.json').write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+'\n',encoding='utf-8')
    print('FV03B:',state,' -> '.join(s['id']+':'+s['status'] for s in stages))
    print('Validation:',output/'VALIDATION_FV03B.json')
    for e in global_errors:print('PREFLIGHT:',e,file=sys.stderr)
    return 0 if state in ('PASS_LOCAL_LEAN','DRY_RUN_ONLY') and not errors else 2


def main(argv=None):
    ap=argparse.ArgumentParser(description='Sequential B1->B2->B3 Lean proof execution and audit')
    ap.add_argument('--out',type=Path,help='New, nonexistent output directory; no overwrites')
    ap.add_argument('--dry-run',action='store_true',help='Inspect prerequisites but do not run Lean')
    a=ap.parse_args(argv)
    out=a.out or ROOT/'FV03B-v0.2.0_outputs'/('run_'+dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'_'+uuid.uuid4().hex[:8])
    try:return run(out.resolve(),a.dry_run)
    except Exception as e:
        print('FV03B_FAIL:',e,file=sys.stderr)
        return 3

if __name__=='__main__':sys.exit(main())
