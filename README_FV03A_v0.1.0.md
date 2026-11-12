# SSTFormal EulerFeedback v0.1.0 — FV03-A

**Scientific status: CONDITIONAL THEOREM PACKAGE / NOT_EXECUTED (until local Lean build).**

Baseline: `SSTFormal ClockEndpoint FV02-C2 v0.5.0`, branch
`sst/formal-clock-euler-c1limsup-v0.5.0`, commit `65f0c27`
(user-reported local Lean PASS). Create a NEW branch
`sst/formal-euler-feedback-v0.1.0`; preserve all existing FV01/FV02 sources.

## 1. Research question

Can a **uniform upper bound on accumulated vortex stretching along all material
trajectories** guarantee a finite bound on vorticity on the half-open interval
\(0\le t<T\), without assuming regularity at the possible singular endpoint \(T\)?

**Yes, conditionally.** The needed rate bound is NOT derived here from Euler's
pressure Hessian, a Ruban trefoil, a Swirl Clock mechanism, or a vortex lattice.

## 2. Physics and dimensional consistency

For incompressible, unforced Euler and vorticity \(\boldsymbol\omega=\nabla\times\mathbf u\),

\[
\partial_t\boldsymbol\omega+(\mathbf u\cdot\nabla)\boldsymbol\omega
 =(\boldsymbol\omega\cdot\nabla)\mathbf u,
 \qquad \nabla\cdot\mathbf u=0.
\]

On a material trajectory \(X(t,a)\), the linear ordinary differential equation
(ODE; gewone differentiaalvergelijking) is

\[
\dot{\boldsymbol\omega}_a=A_a(t)\boldsymbol\omega_a,
\qquad A_a(t)=\nabla\mathbf u(t,X(t,a)).
\]

Define the aligned stretching rate wherever \(\boldsymbol\omega_a\ne0\),

\[
\sigma_{\parallel}(t,a)
 =\frac{\langle\boldsymbol\omega_a,A_a\boldsymbol\omega_a\rangle}
 {\|\boldsymbol\omega_a\|^2}
 =\widehat{\boldsymbol\omega}_a^{\mathsf T}S_a\widehat{\boldsymbol\omega}_a,
\quad S_a=\tfrac12(A_a+A_a^{\mathsf T}).
\]

\(\sigma_\parallel\) has SI dimension \(\mathrm{s}^{-1}\). Its accumulated
integral \(\Phi_a(t)=\int_0^t\sigma_\parallel(s,a)\,ds\) is dimensionless.
\(\|\boldsymbol\omega\|\) has units \(\mathrm{s}^{-1}\).

The *conditional* theorem is

\[
\sup_{a,\;0\le t<T}\Phi_a(t)\le C<\infty
\quad\Longrightarrow\quad
\sup_{a,\;0\le t<T}\|\boldsymbol\omega_a(t)\|
\le e^C\sup_a\|\boldsymbol\omega_a(0)\|.
\]

To conclude a corresponding **Eulerian** spatial supremum, also require
surjectivity of \(a\mapsto X(t,a)\) and exact equality of the transported
vorticity and the Eulerian field. These are explicit Lean premises.

For zero vorticity, the squared-norm law does not divide by zero; the chosen
rate only needs to satisfy the algebraic aligned-rate identity.

## 3. Source layout and proof obligations

| File | Purpose | Core result |
|---|---|---|
| `SSTFormal/EulerFeedback/StretchingBound.lean` | Scalar integrating factor on `[0,T)` | `scalar_stretching_upper_bound` |
| `SSTFormal/EulerFeedback/VorticityBound.lean` | Squared-norm derivative, skew-part cancellation, vorticity bound | `vorticity_norm_bound_before_endpoint` |
| `SSTFormal/EulerFeedback/EulerianTransfer.lean` | Conditional Lagrangian-to-Eulerian transfer | `eulerian_norm_bound_from_trajectory_coverage` |
| `tools/audit_fv03a.py` | Strict local theorem/axiom audit and SHA-256 | `VALIDATION_FV03A_LOCAL.json` |
| `tools/make_app07_fv03a_contract.py` | Existing app_07 v0.2.1 report contract | JSON PDF input |
| `run_sstformal_eulerfeedback_v0.1.0.cmd` | Windows per-module Lean builds | Lean log |
| `tests/test_fv03a.py` | Installer-independent Python tests | Static preflight |

13 Lean theorem declarations. Exactly the permitted axioms
`propext`, `Classical.choice`, and `Quot.sound` **or a subset** must appear after
local compilation. No `sorry`, `admit`, or added `axiom` declarations are intended.

## 4. Installation: no overwrites

In PowerShell or cmd.exe:

```bat
cd C:\workspace\projects\NavierStokesAndEuler
git switch sst/formal-clock-euler-c1limsup-v0.5.0
git switch -c sst/formal-euler-feedback-v0.1.0
```

Extract ZIP to a separate staging folder, then from that folder:

```bat
python install_fv03a.py --repo "C:\workspace\projects\NavierStokesAndEuler"
python install_fv03a.py --repo "C:\workspace\projects\NavierStokesAndEuler" --apply
```

Dry-run by default. Existing changed files cause `INSTALL_REFUSED_CONFLICT`.
No `lakefile.toml`, FV02 sources, or existing validation artifacts are modified.
The installer refuses a mismatched Git branch.

Then, in the repository root:

```bat
python -m unittest discover -s tests -p test_fv03a.py -v
run_sstformal_eulerfeedback_v0.1.0.cmd
```

**Do not claim PASS until the `.cmd` returns exitcode 0 and the strict audit
returns PASS_LOCAL_LEAN.** On failure, send the ending of
`sstformal_eulerfeedback_v0.1.0_build.log`; the audit never relabels an
unexecuted proof as PASS. Existing logs and validation records are never
silently overwritten.

The current release builder cannot run your local Windows Lean 4.34.0-rc2,
therefore **all new Lean modules remain NOT_EXECUTED here.** Static Python
preflight and JSON schema validation are separate results.

## 5. app_07 PDF Visualizer v0.2.1

The package does not alter your PDF Visualizer. Instead generate a native
`report_contract_v1.schema.json`-compatible JSON:

```bat
python tools\make_app07_fv03a_contract.py --contract "FV03A_contract_before_build.json"
```

After a verified local run, create a *new* contract (do not overwrite):

```bat
python tools\make_app07_fv03a_contract.py ^
  --validation "VALIDATION_FV03A_LOCAL.json" ^
  --contract "FV03A_contract_after_build.json"
```

From the installed app_07-v0.2.1 folder, render the generated contract:

```bat
python -m app07 render --contract "C:\workspace\projects\NavierStokesAndEuler\FV03A_contract_after_build.json" --out "C:\workspace\projects\SST-Workbench\05_apps\app_07_PDF_Diagnozer_Analyser_Visualizer\FV03A_Report_001" --engine pdflatex
```

The destination must be new/empty. This outputs `report.pdf`, `contract.pdf`,
LaTeX sources, original JSON, SHA-256 manifest and a REPORT_ONLY ZIP. The
contract contains inputs, 13 theorem goals, status gates, uncertainties, and
open obligations. The PDF renderer is **report only**: no Lean/physics rerun.

## 6. Strict scientific gate classification

| Gate | Description | Initial state |
|---|---|---|
| G0 | Exact source identity / SHA-256 | Can PASS after local hash inspection |
| G1 | Lean typecheck and `#print axioms` (13 targets) | NOT_EXECUTED |
| G2 | Actual Euler partial differential equation (PDE) to material ODE | NOT_EXECUTED |
| G3 | Pressure-Hessian/strain feedback implies a finite stretching cap | UNRESOLVED |
| G4 | Surjective material flow / Eulerian field identification | NOT_EXECUTED |
| G5 | Actual free Ruban trefoil stability | NOT_EXECUTED |
| G6 | Independent Python/C++ versus Intel Arc/NVIDIA CUDA validation | NOT_EXECUTED |
| G7 | Independent formal proof rerun/Comparator | NOT_EXECUTED |

**FV03-A proves an implication, not its antecedent.** It does not establish
non-blowup of all Euler flows, physical SST stabilization, a finite-core
constitutive closure, or any value of a fundamental particle constant.

## 7. Recommended follow-on

- **FV03-B:** derive the strain/pressure-Hessian equation and seek a
  sufficient bound on \(\int\sigma_{\parallel}\,dt\) from genuinely coupled Euler dynamics.
- **FV03-C:** Ruban Trefoil / background lattice with Euler Trajectory Generator
  v0.4.0, Canonical Framework v1.1.2, and two separate actually executed
  verification lanes: Python/C++ reference and Intel Arc or NVIDIA CUDA.

## Bibliography — LaTeX `\bibitem` entries

```latex
\bibitem{Helmholtz1858}
H.~von Helmholtz (1858), "On Integrals of the Hydrodynamical Equations
Which Express Vortex-Motion," Journal fuer die reine und angewandte
Mathematik 55, 25--55. DOI: 10.1515/crll.1858.55.25.

\bibitem{BKM1984}
J.~T.~Beale, T.~Kato, and A.~Majda (1984),
"Remarks on the Breakdown of Smooth Solutions for the 3-D Euler Equations,"
Communications in Mathematical Physics 94, 61--66.
DOI: 10.1007/BF01212349.

\bibitem{Saffman1992}
P.~G.~Saffman (1992), Vortex Dynamics,
Cambridge University Press. DOI: 10.1017/CBO9780511624063.
```
