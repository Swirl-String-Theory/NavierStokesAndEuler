# Execution / reporting example

For Windows (all relative paths below are from the Lean repository root):

```bat
run_sstformal_eulerfeedback_v0.2.0.cmd
```

This creates a fresh directory under `FV03B-v0.2.0_outputs\run_*` with
`B1_PDEtoODE.log`, `B2_PressureHessian.log`, `B3_FlowCoverage.log`, and
`VALIDATION_FV03B.json`. If B1 fails, B2 and B3 are `BLOCKED` and are not run.

Construct a pre-build PDF Visualizer contract (does not execute Lean):

```bat
python tools\make_app07_fv03b_contract.py --contract FV03B_contract_prebuild.json
```

Construct an evidence-matched post-build contract using the `VALIDATION_FV03B.json`
in the actual run output folder (replace the bracketed directory):

```bat
python tools\make_app07_fv03b_contract.py ^
  --validation "FV03B-v0.2.0_outputs\<run_id>\VALIDATION_FV03B.json" ^
  --contract "FV03B_contract_<run_id>.json"
```

Render with existing `app_07-v0.2.1` (run from its root):

```bat
python -m app07 render ^
 --contract "C:\workspace\projects\NavierStokesAndEuler\FV03B_contract_<run_id>.json" ^
 --out "C:\workspace\projects\SST-Workbench\05_apps\app_07_PDF_Diagnozer_Analyser_Visualizer\FV03B_Report_001" ^
 --engine pdflatex
```

The target report directory must be new/empty. `PASS_LOCAL_LEAN` in a PDF is
source-attested only; the scientific status stays `UNRESOLVED`.
