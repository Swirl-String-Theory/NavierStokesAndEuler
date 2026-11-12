"""Offline tests do not execute Lean; local Lean build remains mandatory."""
import importlib.util
import json
import math
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent

def load(name,path):
    import sys
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module
    spec.loader.exec_module(module)
    return module

run=load('run_fv03b',Path('tools/run_fv03b.py'))
contract=load('make_app07_fv03b_contract',Path('tools/make_app07_fv03b_contract.py'))

class FV03BTests(unittest.TestCase):
    def test_stage_order_and_theorem_counts(self):
        self.assertEqual([x[0] for x in run.MODULES],['B1','B2','B3'])
        self.assertEqual([len(x[2]) for x in run.MODULES],[4,5,2])
        self.assertEqual([len(contract.THEOREMS[s]) for s in ('B1','B2','B3')],[4,5,2])

    def test_proof_source_inventory(self):
        for stage,name,targets in run.MODULES:
            source=(ROOT/'SSTFormal'/'EulerFeedback'/(name+'.lean')).read_text(encoding='utf-8')
            for target in targets:
                self.assertIn('theorem '+target,source)
                self.assertIn('#print axioms SSTFormal.EulerFeedback.'+target,source)

    def test_clean_axiom_parser(self):
        names=run.MODULES[0][2]
        log='\n'.join(f"'SSTFormal.EulerFeedback.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
        found,errors=run.parse_axioms(log,names)
        self.assertEqual(len(found),4)
        self.assertEqual(errors,[])

    def test_missing_axiom_record_fails(self):
        found,errors=run.parse_axioms('',run.MODULES[1][2])
        self.assertEqual(len(found),0)
        self.assertEqual(len([x for x in errors if 'MISSING' in x]),5)

    def test_unapproved_axiom_fails(self):
        names=run.MODULES[2][2]
        log='\n'.join(f"'SSTFormal.EulerFeedback.{n}' depends on axioms: [propext, sorryAx]" for n in names)
        _,errors=run.parse_axioms(log,names)
        self.assertTrue(any('SORRYAX' in x or 'DISALLOWED_AXIOM' in x for x in errors))

    def test_error_line_blocks_pass(self):
        names=run.MODULES[2][2]
        log='\n'.join(f"'SSTFormal.EulerFeedback.{n}' does not depend on any axioms" for n in names)
        _,errors=run.parse_axioms(log+'\nerror: failure\n',names)
        self.assertTrue(any('LEAN_ERROR' in x for x in errors))

    def test_independent_open_gates_never_promoted(self):
        stages=[{'id':stage,'status':'PASS_LOCAL_LEAN'} for stage,_,_ in run.MODULES]
        gates={g['id']:g['status'] for g in run.report_stages(stages)}
        self.assertEqual(gates['GB1_FORMAL_PDE_CHAIN'],'PASS')
        self.assertEqual(gates['GB2_RICCATI_IDENTITY'],'PASS')
        self.assertEqual(gates['GB3_FINITE_FLOW_COVERAGE'],'PASS')
        self.assertEqual(gates['G3_NONCIRCULAR_STRETCHING_CAP'],'UNRESOLVED')
        self.assertEqual(gates['G4_MAXIMAL_FLOW_COVERAGE'],'UNRESOLVED')
        self.assertEqual(gates['G6_CPU_GPU'],'NOT_EXECUTED')

    def test_b2_scalar_riccati_toy_not_stabilization(self):
        # Pure scalar Riccati A'=-A^2-H; H=0, A0<0 leads finite blowup.
        # This is an algebraic counterexample, not a 3D Euler solution.
        a0=-2.0
        for t in [0.0,0.1,0.25,0.49]:
            a=a0/(1+a0*t)
            d=-a*a
            self.assertTrue(math.isfinite(d))
            self.assertAlmostEqual(d,-a*a)
        self.assertGreater(abs(a0/(1+a0*.49)),50)

    def test_inverse_flow_example(self):
        # Bounded Lipschitz test flow: u(t,x)=0 on Euclidean space.
        for t in (0.0,0.25,0.75):
            for x in (-3.0,0.0,2.5):
                X=lambda time,label:label
                Y=lambda time,value:value
                self.assertEqual(X(t,Y(t,x)),x)

    def test_prebuild_contract_fails_closed(self):
        c=contract.build()
        self.assertEqual(c['conclusion']['scientific_status'],'UNRESOLVED')
        self.assertTrue(all(s['status']=='NOT_EXECUTED' for s in c['runs']))
        self.assertEqual(c['framework']['verification_status'],'PARTIAL_OR_NOT_EXECUTED')
        self.assertEqual(len(c['methods']),3)

    def test_fail_fast_stage_label(self):
        stages=[{'id':'B1','status':'FAIL'}, {'id':'B2','status':'BLOCKED'}, {'id':'B3','status':'BLOCKED'}]
        gates={g['id']:g['status'] for g in run.report_stages(stages)}
        self.assertEqual(gates['GB1_FORMAL_PDE_CHAIN'],'FAIL')
        self.assertEqual(gates['GB2_RICCATI_IDENTITY'],'BLOCKED')
        self.assertEqual(gates['GB3_FINITE_FLOW_COVERAGE'],'BLOCKED')


    def test_mocked_runner_runs_exactly_b1_b2_b3_in_order(self):
        # Controller test only: fake Lean output is never physical/formal evidence.
        from unittest.mock import patch
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for _,name,_ in run.MODULES:
                source=root/'SSTFormal'/'EulerFeedback'/(name+'.lean')
                source.parent.mkdir(parents=True,exist_ok=True)
                source.write_text('theorem dummy : True := by trivial\n')
            executed=[]
            def fake_lean(args,**_kw):
                name=Path(args[-1]).stem
                executed.append(name)
                (root/args[4]).parent.mkdir(parents=True,exist_ok=True)
                (root/args[4]).write_bytes(b'mocked_olean')
                targets=next(targets for _,module,targets in run.MODULES if module==name)
                msg='\n'.join(f"'SSTFormal.EulerFeedback.{n}' depends on axioms: [propext]" for n in targets)
                return SimpleNamespace(returncode=0,stdout=msg)
            with patch.object(run,'ROOT',root),patch.object(run,'preflight',return_value=[]),\
                 patch.object(run.subprocess,'run',side_effect=fake_lean),\
                 patch.object(run,'git',return_value='mock'):
                rc=run.run(root/'output')
            record=json.loads((root/'output'/'VALIDATION_FV03B.json').read_text())
            self.assertEqual(rc,0)
            self.assertEqual(executed,['PDEtoODE','PressureHessian','FlowCoverage'])
            self.assertEqual(record['status'],'PASS_LOCAL_LEAN')
            self.assertEqual(record['gates'][4]['status'],'UNRESOLVED')

    def test_mocked_runner_stops_immediately_on_b1_error(self):
        from unittest.mock import patch
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for _,name,_ in run.MODULES:
                source=root/'SSTFormal'/'EulerFeedback'/(name+'.lean')
                source.parent.mkdir(parents=True,exist_ok=True)
                source.write_text('theorem dummy : True := by trivial\n')
            executed=[]
            def fake_lean(args,**_kw):
                executed.append(Path(args[-1]).stem)
                return SimpleNamespace(returncode=1,stdout='error: deliberate mock compilation failure')
            with patch.object(run,'ROOT',root),patch.object(run,'preflight',return_value=[]),\
                 patch.object(run.subprocess,'run',side_effect=fake_lean),\
                 patch.object(run,'git',return_value='mock'):
                rc=run.run(root/'output')
            record=json.loads((root/'output'/'VALIDATION_FV03B.json').read_text())
            self.assertEqual(rc,2)
            self.assertEqual(executed,['PDEtoODE'])
            self.assertEqual([s['status'] for s in record['stages']],['FAIL','BLOCKED','BLOCKED'])


    def test_installer_create_only_no_overwrite(self):
        from unittest.mock import patch
        install=load('install_fv03b',Path('install_fv03b.py'))
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)
            (repo/'.git').mkdir()
            (repo/'lakefile.toml').write_text('')
            prior=repo/'SSTFormal'/'EulerFeedback'/'StretchingBound.lean'
            prior.parent.mkdir(parents=True)
            for name in ('StretchingBound.lean','VorticityBound.lean','EulerianTransfer.lean'):
                (prior.parent/name).write_text('historical-unchanged')
            from types import SimpleNamespace
            fake=SimpleNamespace(returncode=0,stdout=install.BRANCH+'\n')
            with patch.object(install.subprocess,'run',return_value=fake):
                self.assertEqual(install.main(['--repo',str(repo)]),0)
                self.assertFalse((repo/'SSTFormal/EulerFeedback/PDEtoODE.lean').exists())
                self.assertEqual(install.main(['--repo',str(repo),'--apply']),0)
                target=repo/'SSTFormal/EulerFeedback/PDEtoODE.lean'
                self.assertTrue(target.is_file())
                target.write_text('different-local-modification')
                self.assertEqual(install.main(['--repo',str(repo),'--apply']),3)
                self.assertEqual((prior.parent/'VorticityBound.lean').read_text(),'historical-unchanged')

if __name__=='__main__':unittest.main()
