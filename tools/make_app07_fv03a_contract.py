"""Create a render-only app_07-v0.2.1 JSON report contract for FV03-A.

No Lean theorem is executed, and absent local evidence is NEVER promoted to PASS.
The renderer will append the complete JSON contract to report.pdf.
"""
from __future__ import annotations
import argparse,hashlib,json,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
LEAN_FILES=[
    'SSTFormal/EulerFeedback/StretchingBound.lean',
    'SSTFormal/EulerFeedback/VorticityBound.lean',
    'SSTFormal/EulerFeedback/EulerianTransfer.lean',
]

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def evidence_file(eid,kind,path,description):
    p=ROOT/path
    if p.is_file():
        return {'id':eid,'kind':kind,'origin':str(p),'sha256':digest(p),
                'verification':'VERIFIED_LOCAL_SHA256','note':description+' Byte hash only; no independent Lean execution.'}
    return {'id':eid,'kind':kind,'origin':str(p), 'sha256':None,
            'verification':'MISSING','note':description+' Missing input.'}

def build_contract(validation_path:Path|None):
    audit=None
    if validation_path is not None:
        if not validation_path.is_file():
            raise ValueError('VALIDATION_FILE_MISSING: '+str(validation_path))
        audit=json.loads(validation_path.read_text(encoding='utf-8'))
        if audit.get('id')!='SST-FV03A':raise ValueError('WRONG_VALIDATION_ID')
    es=[evidence_file('source_'+str(i),'LEAN_SOURCE',x,'FV03-A source') for i,x in enumerate(LEAN_FILES)]
    allowed={'propext','Classical.choice','Quot.sound'}
    audit_good=bool(audit and audit.get('status')=='PASS_LOCAL_LEAN'
       and audit.get('lean_exit_code')==0 and audit.get('no_sorryAx_reported') is True
       and audit.get('theorem_count_checked')==13 and not audit.get('errors')
       and audit.get('execution',{}).get('independent_assistant_execution') is False
       and audit.get('git',{}).get('branch')=='sst/formal-euler-feedback-v0.1.0'
       and all(set(v).issubset(allowed) for v in audit.get('theorems',{}).values()))
    if audit_good:
        orig=audit.get('evidence',{}).get('source_sha256',{})
        # Normalize Windows path keys from local audits to POSIX Lean paths.
        orig={str(Path(k).as_posix()):v for k,v in orig.items()}
        audit_good=all(orig.get(x)==digest(ROOT/x) for x in LEAN_FILES)
    ev_log=evidence_file('local_build_log','LEAN_BUILD_LOG','sstformal_eulerfeedback_v0.1.0_build.log','Local Lean build output')
    es.append(ev_log)
    ev_audit=evidence_file('local_validation','LOCAL_AXIOM_AUDIT','VALIDATION_FV03A_LOCAL.json','Local post-build theorem axiom audit')
    es.append(ev_audit)
    audit_good=audit_good and ev_log['verification']=='VERIFIED_LOCAL_SHA256' and ev_audit['verification']=='VERIFIED_LOCAL_SHA256'
    if audit_good:
        audit_good=(audit.get('evidence',{}).get('build_log_sha256')==ev_log['sha256'])
    proof_ids=['source_'+str(i) for i in range(len(LEAN_FILES))]
    refs=proof_ids+(['local_build_log','local_validation'] if audit_good else [])
    def gate(id, question, status, why, references=None):
        return {'id':id,'question':question,'status':status,'evidence_refs':references or [],'justification':why}
    stages=['weightedInvariant_hasDerivAt_zero', 'weightedInvariant_constant_before_endpoint',
            'scalar_stretching_identity','scalar_stretching_upper_bound','uniform_material_stretching_bound',
            'skew_operator_has_zero_aligned_stretch','aligned_stretch_ignores_skew_part',
            'vorticity_norm_sq_hasDerivAt','vorticity_norm_sq_scalar_law',
            'vorticity_norm_sq_bound_before_endpoint','vorticity_norm_bound_before_endpoint',
            'eulerian_norm_sq_bound_from_trajectory_coverage',
            'eulerian_norm_bound_from_trajectory_coverage']
    gates=[gate('G0_SOURCE','Are all FV03-A source bytes available and hashed?',
        'PASS' if all(e['verification']=='VERIFIED_LOCAL_SHA256' for e in es[:3]) else 'BLOCKED',
        'SHA256 checks only byte identity, not theorem correctness.',proof_ids),
        gate('G1_LEAN','Did the local Lean build accept all 13 theorems with permitted axioms?',
        'PASS' if audit_good else 'NOT_EXECUTED',
        'A verified matching local audit plus build log is required for PASS. No independent CI check.',
        refs if audit_good else []),
        gate('G2_MATERIAL_ODE','Is the material stretching ODE derived from the actual Euler PDE?',
        'NOT_EXECUTED','This stage assumes D_t omega = (grad u) omega; no PDE bridge is provided.'),
        gate('G3_HESSIAN','Is a pressure-Hessian feedback bound sufficient to establish the stretching cap?',
        'UNRESOLVED','The scalar primitive upper bound is a premise, not an Euler pressure-Hessian consequence.'),
        gate('G4_FLOW','Is trajectory coverage/surjectivity proved for the particular Euler field?',
        'NOT_EXECUTED','Coverage is explicit in the eulerian transfer theorem and not yet discharged.'),
        gate('G5_RUBAN','Is a free Ruban Trefoil shown to satisfy the stretching cap?',
        'NOT_EXECUTED','No Ruban geometry, seed, or Euler trajectory supplied.'),
        gate('G6_GPU','Have independent Python/C++ and Intel Arc/CUDA numerical lanes run?',
        'NOT_EXECUTED','Formal Lean code does not execute numerical backends.'),
        gate('G7_INDEPENDENT','Was the Lean proof rerun independently by the report author?',
        'NOT_EXECUTED','The report service renders attestations and checks file hashes only.')]
    methods=[
      {'name':'Unforced incompressible Euler','description':'Continuum reference model; the Lean conditional bounds do not themselves construct a 3D Euler solution.',
       'equations':[{'latex':r'\partial_t\mathbf u+(\mathbf u\cdot\nabla)\mathbf u=-\nabla P,\quad\nabla\cdot\mathbf u=0',
                     'status':'STANDARD'}]},
      {'name':'Material vorticity stretching','description':'Assumed Euler trajectory identity for the operator A(t)=grad u along a material trajectory; this must later be proved in the PDE bridge.',
       'equations':[{'latex':r'\frac{D\boldsymbol\omega}{Dt}=A\boldsymbol\omega,\qquad A=\nabla\mathbf u',
                     'status':'STANDARD'}]},
      {'name':'Aligned stretching and cumulative stretching','description':'The aligned stretching rate is defined only when nonzero vorticity; the Lean squared-norm identity avoids dividing by zero.',
       'equations':[{'latex':r'\sigma_{\parallel}=\frac{\langle\boldsymbol\omega,A\boldsymbol\omega\rangle}{\|\boldsymbol\omega\|^2},\quad \Phi(t)=\int_0^t\sigma_{\parallel}(s)\,ds',
                     'status':'DEFINED', 'caption':'sigma [s^-1]; Phi dimensionless.'}]},
      {'name':'Conditional stretching bound','description':'Proved for a material-vector ODE when the aligned-rate primitive exists and is uniformly upper bounded on the half-open interval.',
       'equations':[{'latex':r'\Phi(t)\leq C\quad(0\leq t<T)\quad\Longrightarrow\quad \|\boldsymbol\omega(t)\|\leq \|\boldsymbol\omega(0)\|e^C',
                     'status':'DEFINED','caption':'Not proved that any specific Euler solution satisfies Phi <= C.'}]},
      {'name':'Full-space transfer','description':'A spatial supremum bound additionally requires exact trajectory coverage and identification of the transported field.',
       'equations':[{'latex':r'X(t,\cdot)\ \text{surjective},\qquad \boldsymbol\omega(t,X(t,a))=\boldsymbol\omega_a(t)',
                     'status':'DEFINED','caption':'These hypotheses are OPEN for the Euler PDE bridge.'}]}
    ]
    raw={'phase':'FV03-A','stage':'conditional stretching bound','status':'PASS_LOCAL_LEAN' if audit_good else 'NOT_EXECUTED',
         'branch':'sst/formal-euler-feedback-v0.1.0','base_branch':'sst/formal-clock-euler-c1limsup-v0.5.0',
         'base_commit':'65f0c27','theorems':stages,
         'inputs':{'T':'finite positive time endpoint; all claims for 0<=t<T',
                   'A':'time-dependent bounded linear velocity-gradient operator along a material trajectory',
                   'sigma':'aligned stretching rate via vector inner product',
                   'Phi':'primitive Phi(0)=0, Phi_prime(t)=sigma(t) for 0<t<T',
                   'bound':'uniform in time and labels: Phi(t)<=C',
                   'no_end_time_smoothness':'No continuity/differentiability at t=T assumed',
                   'constants':'No dimensional SST/particle constants used in Lean'},
         'gates':{g['id']:g['status'] for g in gates},
         'open_proof_obligations':['Derive A=grad u on actual Euler material path',
                                   'Prove global flow coverage without assuming endpoint regularity',
                                   'Establish Phi<=C from pressure-Hessian feedback',
                                   'Test Ruban, independently on Python/C++ and Arc/CUDA'],
         'local_validation':audit if audit else 'NOT_SUPPLIED'}
    return {'contract_version':'1.0.0','report_id':'SSTFormal-FV03A-v010-'+digest(ROOT/LEAN_FILES[0])[:12],
       'family':{'catalog_id':'SST-FV03A','version':'v0.1.0',
         'title':'EulerFeedback: conditional material vorticity stretching bound',
         'plugin':'generic','source_path':str(ROOT)},
       'framework':{'name':'Lean 4, Mathlib, NavierStokesAndEuler formalization',
         'version':'4.34.0-rc2','verification_status':'PASS_LOCAL_LEAN_SOURCE_ATTESTED' if audit_good else 'NOT_EXECUTED',
         'reporter_role':'RENDER_ONLY_NO_SCIENCE_PROMOTION','instance_id':None,'manifest_sha256':None},
       'research':{'question':'Does a uniform upper bound on material integrated vorticity stretching imply a finite bound on actual Eulerian vorticity before a possible singular endpoint?',
         'hypothesis':'A conditional bounded-stretching implication follows for material vorticity, and propagates to full space when flow coverage is separately established.',
         'falsification_criterion':'Fail the formal stage on Lean typecheck errors, disallowed axioms, missing audit, or an invalid transported-vorticity premise; no physical stability claim is permitted without demonstrating the uniform stretching cap.',
         'scope':'Conditional proof only; finite time t<T. No established pressure-Hessian closure, no Ruban stability claim, no numerical solver execution.'},
       'methods':methods,'evidence':es,
       'runs':[{'id':'FV03A_LOCAL_LEAN','backend':'Lean 4 / Mathlib (local user)',
                'status':'PASS' if audit_good else 'NOT_EXECUTED','configuration':raw['inputs'],
                'metrics':{'theorem_count':13,'verified_local_audit':audit_good},
                'evidence_refs':refs if audit_good else [],
                'note':'User-local axioms and source hashes only; no independent assistant execution.'}],
       'gates':gates,
       'conclusion':{'scientific_status':'UNRESOLVED',
          'observed':'Formal stretching implication has been prepared; local Lean acceptance is '+('attested and audited.' if audit_good else 'NOT EXECUTED.'),
          'unresolved':'No physical mechanism establishes the required upper bound on integrated stretching. No actual free Ruban Euler evolution is proved to satisfy it.',
          'next_experiment':'FV03-B formal pressure-Hessian/strain coupling, then FV03-C Ruban Euler trajectories with independent reference and GPU validation.',
          'limitations':['A formal conditional upper bound does not prove stability of every smooth Euler solution.',
                         'The premise Phi<=C may fail for the constructed finite-time Euler blowup solution.',
                         'The full spatial bound needs surjective flow coverage and material identification.',
                         'No continuity at T has been assumed or proved.',
                         'PDF generation is not an independent proof execution.']},
       'references':[{'key':'BKM1984','citation':'J. T. Beale, T. Kato, A. Majda (1984), Remarks on the breakdown of smooth solutions for the 3-D Euler equations, Communications in Mathematical Physics 94, 61-66. DOI 10.1007/BF01212349.'},
          {'key':'Saffman1992','citation':'P. G. Saffman (1992), Vortex Dynamics, Cambridge University Press. DOI 10.1017/CBO9780511624063.'},
          {'key':'EulerFormal2026','citation':'OpenAI (2026), Finite Time Blowup for the Euler Equation, formalization repository https://github.com/openai/NavierStokesAndEuler.'}],
       'series':[], 'raw_source':raw,
       'report_options':{'include_contract_appendix':True,'language':'en',
            'title':'SST-FV03A - EulerFeedback Conditional Vorticity Stretching'}}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--validation',type=Path)
    p.add_argument('--contract',required=True,type=Path)
    args=p.parse_args()
    out=args.contract.resolve()
    if out.exists():raise SystemExit('REFUSE_OVERWRITE: '+str(out))
    contract=build_contract(args.validation.resolve() if args.validation else None)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(contract,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print('Wrote',out,'status:',contract['framework']['verification_status'])

if __name__=='__main__':sys.exit(main())
