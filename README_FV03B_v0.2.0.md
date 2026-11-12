# SSTFormal EulerFeedback v0.2.0 — FV03-B1/B2/B3 sequential package

**Scientific status:** UNRESOLVED.  **New Lean code:** NOT EXECUTED in the
packaging environment.  **Python package tests:** 14/14 PASS (offline, not a
Lean typecheck). This version is intended as an additive development branch,
not a certified Euler regularity or SST vortex-stabilization result.

## 0. Baseline and invariants

- Parent: `sst/formal-euler-feedback-v0.1.0`, commit `357fd80` (locally
  PASS_USER_REPORTED, 13/13 theorems and 7/7 Python tests).
- New branch: `sst/formal-euler-feedback-v0.2.0`.
- Toolchain: `leanprover/lean4:v4.34.0-rc2`, matching existing `lean-toolchain`.
- **No modifications** to any FV01/FV02/FV03-A Lean source, `lakefile.toml`,
  canonical SST constants, Euler original proofs or past output archives.
- Three **independently audited**, strictly ordered Lean stages with fail-fast.
  Later stages are BLOCKED if an earlier stage fails.
- No `sorry`, `admit`, new `axiom` or unapproved imported axiom is permitted.
- Every actual local Lean PASS must be supported by a *successful process
  exit*, a newly generated `.olean`, the complete `#print axioms` inventory,
  and the corresponding SHA-256 source/log records.

## 1. Research question and hypotheses

Can (i) the material vorticity ordinary differential equation (ODE), (ii)
pressure-Hessian/velocity-gradient feedback and (iii) material trajectory
coverage be investigated **in one sequential formal validation version**, with
physical assumptions visible rather than promoted into conclusions?

**Yes:** all three developments are in this release. **No general regularity
result is claimed.** Deriving a *uniform* integrated-stretching cap from
pressure alone remains the falsifiable, unresolved part of G3.

### B1 — Euler PDE to material ODE

For smooth, incompressible, unforced three-dimensional Euler,

\[
\partial_t\mathbf u+(\mathbf u\cdot\nabla)\mathbf u=-\nabla p,
\qquad \nabla\cdot\mathbf u=0,\qquad
\boldsymbol\omega=\nabla\times\mathbf u.
\]

Using the curl-convection identity and curl of a pressure gradient,

\[
\partial_t\boldsymbol\omega+(\mathbf u\cdot\nabla)\boldsymbol\omega
   =(\boldsymbol\omega\cdot\nabla)\mathbf u.
\]

Along a true material path \(\dot{\mathbf X}=\mathbf u(t,\mathbf X)\),

\[
\frac{d}{dt}\boldsymbol\omega(t,\mathbf X(t,\mathbf a))
   =A(t,\mathbf X(t,\mathbf a))\boldsymbol\omega(t,\mathbf X(t,\mathbf a)),
\qquad A=\nabla\mathbf u.
\]

**Formal scope:** `PDEtoODE.lean` derives the spatial curl identity from the
Euler momentum equation and chain rule. Time-curl commutation and spacetime
mixed differentiability remain *named regularity premises*. They are not yet
instantiated against the specific maximal solution in `Euler.Solution`.
Thus B1-formal PASS (if locally typechecked) is not automatically full G2
instantiation PASS.

### B2 — Pressure Hessian / strain coupling

Let \(A_{ij}=\partial_j u_i\), \(H_{ij}=\partial_i\partial_j p\) (pressure per
unit mass; kinematic pressure). Along a trajectory:

\[
\frac{DA}{Dt}=-A^2-H,\qquad
S=\tfrac12(A+A^\mathsf T),\quad W=\tfrac12(A-A^\mathsf T).
\]

Expanding \(A=S+W\) formally yields

\[
\frac{DS}{Dt}=-(S^2+W^2)-H,\qquad
\frac{DW}{Dt}=-(SW+WS),
\]

**provided** the regularity, symmetry and projection conditions hold.
`PressureHessian.lean` checks the operator Riccati algebra, its expansion,
the aligned-skew cancellation, and the inequality

\[
\|A'(t)\|\le\|A(t)\|^2+\|H(t)\|.
\]

The displayed evolution of the symmetric/antisymmetric components is a
*mathematical consequence under the above symmetry assumptions*, not a
separately Lean-certified theorem in this first version. Moreover, bounding
\(H\) does not provide a non-circular uniform upper bound on
\(\Phi_a(t)=\int_0^t\sigma_\parallel(s,a)ds\). **G3 remains UNRESOLVED** even if
B2 compiles. In particular, FV03-A's \(\Phi_a(t)\le C\) premise is *not* recycled
as a derived conclusion.

### B3 — Material-flow coverage

The existing `Euler.FiniteIntervalFlow` theorem constructs a flow \(X\) and
inverse \(Y\) for a bounded jointly continuous, uniformly Lipschitz velocity
on a **finite regular horizon** \([0,S]\):

\[
X(t,Y(t,x))=x,\qquad Y(t,X(t,a))=a.
\]

`FlowCoverage.lean` extracts surjectivity and composes it with FV03-A's
Eulerian bound-transfer theorem. No surjectivity assumption is smuggled in.
For the maximal half-open lifespan \([0,T_*)\), the velocity must satisfy the
finite-horizon hypotheses for *each* \(S<T_*\), and the Eulerian vorticity
must equal the actual material transport. This maximal-Euler instantiation
remains open; no endpoint regularity is assumed.

## 2. Stage layout

| Stage | Lean source | New theorems | Build consequence |
|---|---|---:|---|
| B1 | `SSTFormal/EulerFeedback/PDEtoODE.lean` | 4 | prerequisite of B2 |
| B2 | `SSTFormal/EulerFeedback/PressureHessian.lean` | 5 | prerequisite of B3; non-circular cap still open |
| B3 | `SSTFormal/EulerFeedback/FlowCoverage.lean` | 2 | conditional finite-horizon coverage |

**Total: 11 new theorem declarations**, individually checked with `#print axioms`.
Note: prior FV03-A had 13 stellingen; it remains untouched.

## 3. Install into existing Git fork on Windows

```bat
cd C:\workspace\projects\NavierStokesAndEuler
git status --short
git switch sst/formal-euler-feedback-v0.1.0
git switch -c sst/formal-euler-feedback-v0.2.0
```

Extract this ZIP into a **separate staging directory**. From staging:

```bat
python install_fv03b.py --repo "C:\workspace\projects\NavierStokesAndEuler"
python install_fv03b.py --repo "C:\workspace\projects\NavierStokesAndEuler" --apply
```

The installer is dry-run by default and **create-only**. Any nonidentical
existing destination file blocks installation; no source is overwritten.

Then in the *repository root*:

```bat
python -m unittest discover -s tests -p test_fv03b.py -v
run_sstformal_eulerfeedback_v0.2.0.cmd
```

Outputs are immutable run-specific directories:

```
FV03B-v0.2.0_outputs/run_<timestamp>_<nonce>/
  B1_PDEtoODE.log
  B2_PressureHessian.log            (only if B1 passes)
  B3_FlowCoverage.log                (only if B1 and B2 pass)
  VALIDATION_FV03B.json
```

On the first Lean error, later stages stay `BLOCKED`. A successful Python
test does **not** promote a Lean gate. Reruns create a fresh output directory.
The local runner checks exact branch, parent-commit ancestry, fixed
`lean-toolchain`, source existence, exit codes, `.olean` files and axioms.

### Error recovery

When B1, B2 or B3 fails, inspect its log in the new outputs directory. Correct
the module **on the new branch** (never rewrite v0.1.0) and rerun; the runner
creates a new output directory. Preserve previous failed runs as evidence.
Any unexecuted downstream stage is `BLOCKED` even if its source parses.

## 4. PDF Visualizer v0.2.1 integration

The package uses the *existing*, unmodified app_07 report contract:

```bat
python tools\make_app07_fv03b_contract.py --contract FV03B_prebuild_contract.json
```

After a real local run, replace `<run_id>` with the output folder name:

```bat
python tools\make_app07_fv03b_contract.py ^
 --validation "FV03B-v0.2.0_outputs\<run_id>\VALIDATION_FV03B.json" ^
 --contract "FV03B_contract_<run_id>.json"
```

From your installed PDF Visualizer v0.2.1, render using:

```bat
python -m app07 render ^
 --contract "C:\workspace\projects\NavierStokesAndEuler\FV03B_contract_<run_id>.json" ^
 --out "C:\workspace\projects\SST-Workbench\05_apps\app_07_PDF_Diagnozer_Analyser_Visualizer\FV03B_Report_001" ^
 --engine pdflatex
```

Output folder must be new/empty. `report.pdf`, `contract.pdf`, the full JSON
contract, bibliography, gate inventory, logs/provenance identifiers and
`REPORT_ONLY.zip` will be generated. Existing app_07 modules are not changed.

## 5. Gate policy / non-circularity

| Gate | If B1–B3 Lean pass | Meaning |
|---|---|---|
| GB1_FORMAL_PDE_CHAIN | PASS | Smooth Euler curl + material chain derivation under explicit hypotheses |
| GB2_RICCATI_IDENTITY | PASS | Riccati algebra and norm, not stability |
| GB3_FINITE_FLOW_COVERAGE | PASS | A constructed inverse for finite horizons |
| G2_ACTUAL_EULER_INSTANTIATION | UNRESOLVED | Requires concrete maximal-solution regularity derivation |
| G3_NONCIRCULAR_STRETCHING_CAP | UNRESOLVED | Must prove cap from PDE without assuming cap |
| G4_MAXIMAL_FLOW_COVERAGE | UNRESOLVED | Must show hypotheses hold on all S<T* and identify vorticity |
| G5_RUBAN | NOT_EXECUTED | No geometry or finite-core validation |
| G6_CPU_GPU | NOT_EXECUTED | No reference/GPU simulation run |
| G7_INDEPENDENT_LEAN | NOT_EXECUTED | No second-kernel Comparator or independent CI run |

A formal conditional theorem does not establish stable Ruban dynamics or SST
particle structure. For a separate numerical phase, use Euler Trajectory
Generator v0.4.0 + Canonical Framework v1.1.2 + Ruban Trefoil and independent
Python/C++ and Intel Arc/NVIDIA CUDA lanes. Never mark an unrun backend PASS.

## 6. Bibitems

```latex
\begin{thebibliography}{99}
\bibitem{Helmholtz1858}
H. von Helmholtz (1858), On Integrals of the Hydrodynamical Equations Which
Express Vortex-Motion, Journal fuer die reine und angewandte Mathematik
55, 25--55. DOI: 10.1515/crll.1858.55.25.
\bibitem{BKM1984}
J. T. Beale, T. Kato, and A. Majda (1984), Remarks on the Breakdown
of Smooth Solutions for the 3-D Euler Equations, Communications in
Mathematical Physics 94, 61--66. DOI: 10.1007/BF01212349.
\bibitem{Saffman1992}
P. G. Saffman (1992), Vortex Dynamics, Cambridge University Press.
DOI: 10.1017/CBO9780511624063.
\bibitem{EulerFormal2026}
OpenAI (2026), Finite Time Blowup for the Euler Equation,
formal proof repository, https://github.com/openai/NavierStokesAndEuler.
\end{thebibliography}
```
