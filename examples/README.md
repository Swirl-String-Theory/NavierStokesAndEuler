# app_07 v0.2.1 integration

Generate report contract on the TARGET PC so source paths, log locations and
SHA-256 hashes refer to the user's actual checkout (not the release builder).

1. `python tools/make_app07_fv03a_contract.py --contract FV03A_contract_prebuild.json`
2. Compile Lean using the `.cmd` script and review `VALIDATION_FV03A_LOCAL.json`.
3. `python tools/make_app07_fv03a_contract.py --validation VALIDATION_FV03A_LOCAL.json --contract FV03A_contract_postbuild.json`
4. In app_07-v0.2.1: `python -m app07 render --contract <full-path> --out <new-empty-dir> --engine pdflatex`.

A prebuild report is **NOT_EXECUTED**, and a postbuild report is source-attested
**PASS_LOCAL_LEAN** only if all 13 axiom audits are present, permitted, and their
source/log hashes match. Independent scientific certification is not implied.
