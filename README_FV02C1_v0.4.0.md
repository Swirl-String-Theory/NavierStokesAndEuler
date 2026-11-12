# SSTFormal ClockEndpoint v0.4.0 — FV02-C1

**Status: NOT EXECUTED.** Candidate Lean formalization; not a certified result until local build and axiom checks succeed.

## Goal
Bridge the already verified real-valued endpoint theorem (FV02-B) to the **actual maximal Euler C¹ norm**, then pass to the equivalent extended-nonnegative (`ENNReal.ofReal`) threshold formulation.

## Pinned predecessor

- FV02-B branch: `sst/formal-clock-endpoint-v0.3.0`
- User-reported commit: `82a4341`
- Toolchain: `leanprover/lean4:v4.34.0-rc2`
- User-reported local compilation: exitcode 0, no `sorryAx`, only `propext`, `Classical.choice`, `Quot.sound`
- Existing `SSTFormal/ClockIntegral.lean` is not overwritten.

## Install on Windows

```powershell
cd C:\workspace\projects\NavierStokesAndEuler
git status --short
git switch sst/formal-clock-endpoint-v0.3.0
git switch -c sst/formal-clock-euler-c1-v0.4.0
```

Extract the ZIP *contents* into that repository root, alongside `lakefile.toml`. Run:

```powershell
.\run_sstformal_clockeulerc1_v0.4.0.cmd
$LASTEXITCODE
```

The script compiles Stage A, then Stage B, then the new `ClockEulerC1.lean`, retaining the existing `.lake` cache. If Lean reports a type mismatch, preserve the log and make only a localized fix in the v0.4.0 branch; do not modify the prior verified proof files.

## Statements

1. `eulerC1RealProfile_eq`: identifies the actual Euler C¹ norm on the physical time interval.
2. `eulerC1RealProfile_unboundedNearLeft`: obtains endpoint blow-up from the existing Euler proof.
3. `eulerC1_unbounded_after_integrated_clock`: composes Euler blow-up with the verified clock-integral inverse.
4. `ennUnboundedNearLeft_of_real`: lifts arbitrary real thresholds to finite `ENNReal` thresholds.
5. `eulerC1ENN_unbounded_after_integrated_clock`: extended-nonnegative threshold statement for the integrated passive clock.
6. `eulerC1_ofReal_eq_comparator`: identifies `ENNReal.ofReal` of the maximal Euler C¹ norm with the comparator's `Euler.velocityC1Norm` at each physical time.

The repository's `Euler/ComparatorSingularityNorms.lean` contains the existing norm-identification theorem. `Euler/EulerC1Breakdown.lean` proves arbitrarily large *actual* maximal C¹ values near the singularity.

## Scientific boundaries

- FV02-C1 concerns **endpoint-unboundedness for the actual Euler norm** and its extended-nonnegative threshold formulation. It does **not** yet prove a separately stated `Filter.limsup ... = ⊤` theorem for the clock-changed field.
- FV02-C2 should prove the `Filter.limsup` statement directly for the clock reparameterization.
- `q : ℝ → ℝ` remains globally continuous and strictly positive. Physical-interval-only and almost-everywhere positivity remain OPEN.
- No singularity is regularized by a *passive* clock reparameterization; **active feedback remains untested**.
- Constant-blind: no quantum-calibration constants appear in this Lean module.

## Validation instructions

Record exact branch and commit, local exitcode, outputs of each `#print axioms`, and an independent check of the final proof (if performed). Keep the predecessor record immutable. A local Lean PASS is not a proof of correctness of any unformalized SST physical assumptions.

## Bibliography (LaTeX)

```latex
\bibitem{OpenAI2026Euler}
OpenAI (2026).
Finite Time Blowup for the Euler Equation.
Research preprint.
https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf

\bibitem{Mathlib2020}
The mathlib Community (2020).
The Lean Mathematical Library.
Proceedings of the 9th ACM SIGPLAN International Conference
on Certified Programs and Proofs, 367--381.
doi:10.1145/3372885.3373824
```
