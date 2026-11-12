"""Truthful app_07 v0.2.x JSON report contract for SST-FV03-B1/B2/B3.

Converts local sequential validator output into a render-only contract.
Never infers formal PASS from source presence, Python tests or PDF output.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys

# Allow `from run_fv03b import ...` when invoked as tools\make_app07_fv03b_contract.py
sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT=Path(__file__).resolve().parent.parent
NAMES={'B1':'PDEtoODE','B2':'PressureHessian','B3':'FlowCoverage'}
THEOREMS={
'B1':['euler_momentum_implies_curl_balance','euler_momentum_implies_material_curl_rhs','material_chain_rule_to_linear_ode','smooth_euler_material_vorticity_ode'],
'B2':['gradient_riccati_rhs_norm_le','pressure_hessian_balance_at_time','material_gradient_derivative_norm_le','riccati_strain_rotation_decomposition','pressure_strain_alignment_of_skew_decomposition'],
'B3':['finite_horizon_material_flow_covers_space','finite_horizon_material_bound_implies_eulerian_bound'],
}
ALLOWED={'propext','Classical.choice','Quot.sound'}

def sha(p:Path)->str:return hashlib.sha256(p.read_bytes()).hexdigest()

def evidence_file(id,kind,path,note):
    p=Path(path).resolve()
    return {'id':id,'kind':kind,'origin':str(p),
            'sha256':sha(p) if p.is_file() else None,
            'verification':'VERIFIED_LOCAL_SHA256' if p.is_file() else 'MISSING',
            'note':note+' SHA256 proves byte identity, not independent theorem verification.'}

def validate_stage(stage):
    code=stage['id'];name=NAMES[code]
    src=ROOT/'SSTFormal'/'EulerFeedback'/(name+'.lean')
    if not src.is_file() or stage.get('source_sha256')!=sha(src):return False
    if stage.get('status')!='PASS_LOCAL_LEAN' or stage.get('lean_exit_code')!=0:return False
    if stage.get('errors') or stage.get('theorem_count')!=len(THEOREMS[code]):return False
    expected={'SSTFormal.EulerFeedback.'+s for s in THEOREMS[code]}
    axioms=stage.get('axioms') or {}
    if set(axioms)!=expected or not all(set(v).issubset(ALLOWED) for v in axioms.values()):return False
    p=Path(stage['log_file'] or '')
    if not p.is_file() or sha(p)!=stage.get('log_sha256'):return False
    # Exact log audit, independently repeated at contract conversion time.
    from run_fv03b import parse_axioms
    found,errors=parse_axioms(p.read_text(encoding='utf-8',errors='replace'),tuple(THEOREMS[code]))
    if errors or found!=axioms:return False
    return bool(stage.get('olean_sha256'))

def build(validation:Path|None=None):
    raw=None; st={}
    if validation:
        raw=json.loads(validation.read_text(encoding='utf-8'))
        if raw.get('id')!='SST-FV03B' or raw.get('version')!='v0.2.0' or raw.get('git',{}).get('branch')!='sst/formal-euler-feedback-v0.2.0':
            raise ValueError('INVALID_VALIDATION_ID_OR_VERSION')
        for s in raw.get('stages',[]):
            if s['id'] in st:raise ValueError('DUPLICATE_STAGE')
            st[s['id']]=s
    es=[]
    for code,name in NAMES.items():
        es.append(evidence_file('source_'+code,'LEAN_SOURCE',ROOT/'SSTFormal'/'EulerFeedback'/(name+'.lean'),
                                code+' proof source'))
    if validation:es.append(evidence_file('local_validation','LOCAL_AXIOM_AUDIT',validation,'Local run audit'))
    checked={k:bool(raw and k in st and validate_stage(st[k])) for k in NAMES}
    for code,s in st.items():
        if code not in NAMES:continue
        if s.get('log_file'):
            es.append(evidence_file('local_log_'+code,'LEAN_BUILD_LOG',s['log_file'],code+' local Lean log'))
    ev={e['id']:e for e in es}
    def proof_refs(code):
        ids=['source_'+code]
        if checked[code]:ids += ['local_validation','local_log_'+code]
        return ids
    def gate(code,question):
        if checked[code]:status='PASS'
        else:
            source_status=st.get(code,{}).get('status','NOT_EXECUTED')
            status=source_status if source_status in ('FAIL','BLOCKED','NOT_EXECUTED') else 'NOT_EXECUTED'
        return {'id':'G'+code+'_FORMAL','question':question,'status':status,
                'evidence_refs':proof_refs(code) if checked[code] else [],
                'justification':('Local Lean proof and axioms attested; source and log SHA256 verified; no independent kernel rerun.'
                                 if checked[code] else 'No acceptable local Lean evidence for this stage. '+
                                 ('Raw stage status: '+st.get(code,{}).get('status','MISSING')))}
    gs=[gate('B1','Is the smooth Euler PDE-to-material-ODE bridge typechecked with explicit commutation/regularity prerequisites?'),
        gate('B2','Are Riccati/pressure-Hessian identities and bounds checked without inferring a stretching cap?'),
        gate('B3','Is finite-horizon surjective flow constructed under bounded-Lipschitz assumptions?')]
    gs += [
      {'id':'G2_EULER_SOLUTION','question':'Are B1 hypotheses proved for the specific maximal Euler field in Euler.Solution?',
        'status':'UNRESOLVED','evidence_refs':[],
        'justification':'No direct instantiation of time-curl commutation and joint chain regularity on the maximal Euler field.'},
      {'id':'G3_NONCIRCULAR_CAP','question':'Does pressure-Hessian feedback prove a uniform integrated stretching cap?',
        'status':'UNRESOLVED','evidence_refs':[],
        'justification':'Riccati identities and operator norm bounds do not bound Phi from above.'},
      {'id':'G4_MAXIMAL_COVERAGE','question':'Are bounded-Lipschitz hypotheses and material identification established for every S<T* of Euler.Solution?',
        'status':'UNRESOLVED','evidence_refs':[],
        'justification':'Finite-horizon flow theorem is conditional on actual regularity estimates for each horizon.'},
      {'id':'G5_RUBAN','question':'Has the Ruban Trefoil been tested for stretching stability?',
        'status':'NOT_EXECUTED','evidence_refs':[],'justification':'No Euler trajectory or Ruban seed computation in Lean release.'},
      {'id':'G6_NUMERICS','question':'Have Python/C++ and Arc/CUDA numerical validation paths both executed?',
        'status':'NOT_EXECUTED','evidence_refs':[],'justification':'Only formal proof/finite software tests, not actual numerical Euler backends.'},
      {'id':'G7_INDEPENDENT','question':'Did an independent Comparator/CI kernel rerun validate the three new stages?',
        'status':'NOT_EXECUTED','evidence_refs':[],'justification':'Local Lean build and source-hash verification do not constitute independent rerun.'},
    ]
    runs=[]
    for code,name in NAMES.items():
        state=gs[list(NAMES).index(code)]['status']
        runs.append({'id':'LEAN_'+code,'backend':'Lean 4.34.0-rc2 (user-local)',
                     'status':'PASS' if state=='PASS' else state,
                     'configuration':{'module':'SSTFormal.EulerFeedback.'+name,
                                      'base':'FV03-A commit 357fd80',
                                      'expected_branch':'sst/formal-euler-feedback-v0.2.0'},
                     'metrics':{'expected_theorems':len(THEOREMS[code]),
                                'local_lean_accepted':checked[code]},
                     'evidence_refs':proof_refs(code) if checked[code] else [],
                     'note':'Sequential stage '+code+'; no interpretation as numerical physics certification.'})
    methods=[
      {'name':'Incompressible Euler and material curl transport',
       'description':'PDE curl identity for smooth divergence-free velocity and pressure, with curl-time commutation and trajectory chain rule explicit.',
       'equations':[{'latex':r'\partial_t\mathbf{u}+(\mathbf{u}\cdot\nabla)\mathbf{u}=-\nabla p,\quad \nabla\cdot\mathbf{u}=0',
                     'status':'STANDARD'},
                    {'latex':r'\frac{D\boldsymbol{\omega}}{Dt}=(\boldsymbol{\omega}\cdot\nabla)\mathbf{u}',
                     'status':'STANDARD','caption':'Conditional on smooth Euler field and time-space curl commutation.'}]},
      {'name':'Pressure-Hessian and velocity-gradient feedback',
       'description':'Material Riccati evolution includes Hessian of kinematic pressure; an a priori cap is NOT established.',
       'equations':[{'latex':r'\frac{D A}{Dt}=-A^2-H,\quad A=\nabla\mathbf{u},\quad H=\nabla\nabla p',
                     'status':'STANDARD'},
                    {'latex':r'\lVert A^{\prime}\rVert\leq \lVert A\rVert^2+\lVert H\rVert',
                     'status':'DEFINED','caption':'Norm bound does not imply bounded cumulative aligned stretching.'}]},
      {'name':'Finite-horizon flow coverage',
       'description':'Existence of a two-sided inverse for the bounded Lipschitz finite-interval flow; no endpoint regularity is assumed.',
       'equations':[{'latex':r'X(t,Y(t,x))=x,\quad 0\leq t\leq S<T_*',
                     'status':'DEFINED'}]},
    ]
    observed=('All three stages locally typechecked and attested.' if all(checked.values())
              else 'Only the displayed stages with matching local Lean evidence are typechecked; remaining stages are not accepted.')
    return {
      'contract_version':'1.0.0',
      'report_id':'SSTFormal-FV03B-v020-'+sha(ROOT/'SSTFormal/EulerFeedback/PDEtoODE.lean')[:12],
      'family':{'catalog_id':'SST-FV03B','version':'v0.2.0','title':'EulerFeedback — sequential B1/B2/B3 formal analysis',
                'plugin':'generic','source_path':str(ROOT)},
      'framework':{'name':'Lean 4 / Mathlib / Euler formalization','version':'4.34.0-rc2',
                   'verification_status':'PASS_LOCAL_LEAN_SOURCE_ATTESTED' if all(checked.values()) else 'PARTIAL_OR_NOT_EXECUTED',
                   'reporter_role':'RENDER_ONLY_NO_SCIENCE_PROMOTION','instance_id':None,'manifest_sha256':None},
      'research':{
         'question':'Can Euler momentum/curl, pressure-Hessian Riccati coupling and finite-horizon material-flow coverage be verified in one strictly ordered formal research version?',
         'hypothesis':'B1 proves the smooth material vorticity ODE, B2 tests exact Riccati algebra, and B3 constructs finite-horizon material coverage, under visible assumptions.',
         'falsification_criterion':'Any Lean typecheck failure, omitted axiom record, disallowed axiom, missing source/log, or hidden physical-closure assumption blocks promotion of its stage.',
         'scope':'Conditional proof development only. Formal typechecking is not a general Euler regularity proof; no pressure-induced stabilization or knot stability result.'},
      'methods':methods,'evidence':es,'runs':runs,'gates':gs,
      'conclusion':{'scientific_status':'UNRESOLVED','observed':observed,
        'unresolved':'Non-circular pressure-Hessian closure, instantiation on maximal Euler field, all-horizon trajectory identification and Ruban stability remain open.',
        'next_experiment':'Discharge time-curl commutation from exact Euler.Solution regularity; derive truly sufficient pressure-Hessian condition or falsify closure; link finite-horizon flows consistently across S<T*.',
        'limitations':['No proof that any regularity bound on pressure Hessian alone yields Phi<=C.',
                       'The finite-horizon flow theorem assumes bounded, Lipschitz velocity on [0,S].',
                       'No smoothness at the potential singular endpoint T* was assumed.',
                       'No Python/C++ versus GPU execution was performed.',
                       'The PDF engine renders evidence; it never certifies the fluid model.']},
      'references':[{'key':'Helmholtz1858','citation':'H. von Helmholtz (1858), On Integrals of the Hydrodynamical Equations Which Express Vortex-Motion, Journal fuer die reine und angewandte Mathematik 55, 25-55, DOI:10.1515/crll.1858.55.25.'},
                    {'key':'BKM1984','citation':'J. T. Beale, T. Kato, A. Majda (1984), Remarks on the Breakdown of Smooth Solutions for the 3-D Euler Equations, Commun. Math. Phys. 94, 61-66, DOI:10.1007/BF01212349.'},
                    {'key':'Saffman1992','citation':'P. G. Saffman (1992), Vortex Dynamics, Cambridge University Press, DOI:10.1017/CBO9780511624063.'}],
      'series':[],'raw_source':{'validation':raw if raw else {'status':'NOT_EXECUTED'},
                               'stage_goal_inventory':THEOREMS,
                               'admitted_physics':'none; conditional hypotheses explicit'},
      'report_options':{'include_contract_appendix':True,'language':'en',
                        'title':'SST-FV03B v0.2.0 — Euler PDE, Pressure Hessian and Flow Coverage'}
    }

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--validation',type=Path)
    p.add_argument('--contract',type=Path,required=True)
    a=p.parse_args()
    out=a.contract.resolve()
    if out.exists():raise SystemExit('REFUSE_OVERWRITE: '+str(out))
    c=build(a.validation.resolve() if a.validation else None)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(c,indent=2,ensure_ascii=True,sort_keys=True)+'\n',encoding='utf-8')
    print('CONTRACT_GENERATED:',out,'verification:',c['framework']['verification_status'])

if __name__=='__main__':main()
