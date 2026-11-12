import importlib.util
import pathlib
import tempfile
import unittest

ROOT=pathlib.Path(__file__).resolve().parent.parent

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

class FV03ATest(unittest.TestCase):
    def test_no_admits(self):
        import re
        files=list((ROOT/'SSTFormal/EulerFeedback').glob('*.lean'))
        self.assertEqual(len(files),3)
        for f in files:
            txt=f.read_text(encoding='utf-8')
            # Permit prose that mentions sorry, but not actual declarations or tactics.
            self.assertNotRegex(txt,r'(?m)^\s*(?:sorry|admit|axiom)\b')
            self.assertIn('#print axioms',txt)
    def test_theorem_inventory(self):
        audit=load('audit', 'tools/audit_fv03a.py')
        self.assertEqual(len(audit.THEOREMS),13)
        src='\n'.join(x.read_text(encoding='utf-8') for x in (ROOT/'SSTFormal/EulerFeedback').glob('*.lean'))
        for name in audit.THEOREMS:
            self.assertIn('theorem '+name,src)
    def test_audit_requires_every_theorem(self):
        audit=load('audit','tools/audit_fv03a.py')
        found,errors=audit.audit("'SSTFormal.EulerFeedback.scalar_stretching_identity' depends on axioms: [propext]")
        self.assertTrue(any('MISSING_PRINT_AXIOMS' in e for e in errors))
    def test_audit_rejects_sorry(self):
        audit=load('audit','tools/audit_fv03a.py')
        _,errors=audit.audit("'SSTFormal.EulerFeedback.scalar_stretching_identity' depends on axioms: [sorryAx]")
        self.assertTrue(any('DISALLOWED_AXIOMS' in e for e in errors))
    def test_report_contract_schema_shape(self):
        builder=load('report','tools/make_app07_fv03a_contract.py')
        r=builder.build_contract(None)
        self.assertEqual(r['contract_version'],'1.0.0')
        self.assertEqual(r['runs'][0]['status'],'NOT_EXECUTED')
        self.assertEqual(r['conclusion']['scientific_status'],'UNRESOLVED')
        self.assertEqual(r['gates'][1]['status'],'NOT_EXECUTED')
        self.assertEqual(len(r['raw_source']['theorems']),13)

if __name__=='__main__':unittest.main()

class AnalyticSanityChecks(unittest.TestCase):
    """Independent analytic examples: not a numerical Euler solver validation."""
    def test_bounded_accumulated_stretch(self):
        import math
        C=2.0
        for k in range(1001):
            t=8.0*k/1001.0
            phi=1.0-math.cos(t)  # integral_0^t sin(s) ds
            w=math.exp(phi)       # solution of w'=sin(t)*w, w(0)=1
            self.assertLessEqual(w, math.exp(C)*(1+1e-13))
    def test_unbounded_cumulative_stretch_example(self):
        import math
        T=1.0
        vals=[]
        for n in (2,4,8,16,32):
            t=T*(1.0-1.0/n)
            phi=-math.log(1.0-t/T)
            w=1.0/(1.0-t/T)
            self.assertAlmostEqual(w,math.exp(phi))
            vals.append(phi)
        self.assertTrue(all(x<y for x,y in zip(vals,vals[1:])))
        # No finite bound as t approaches T; antecedent of FV03-A fails.
