# SSTFormal ClockEndpoint v0.3.0 — SST-FV02 Stage B

**Status: NOT EXECUTED / Lean compilation is required locally.** This is an additive Lean 4 research patch, not a replacement for the pinned OpenAI Euler formalizations.

## Verified predecessor

- FV01 branch: `sst/formal-passive-clock-v0.1.0`, user-reported commit `f29de7a`, `PASS_LOCAL_LEAN`.
- FV02-A branch: `sst/formal-clock-endpoint-v0.2.0`, user-reported commit `553a61f`, `PASS_LOCAL_LEAN`.
- Lean toolchain: pinned `leanprover/lean4:v4.34.0-rc2` (from repository `lean-toolchain`).

FV02-A already proves that endpoint-unboundedness of a real-valued observable is preserved by an `EndpointClockCorrespondence`. FV02-B **derives that correspondence** from a continuous, everywhere strictly positive clock rate.

## Installation (existing Windows clone)

Run from `C:\workspace\projects\NavierStokesAndEuler` in PowerShell:

```powershell
# Protect an uncommitted local working tree before switching branches.
git status --short
git switch sst/formal-clock-endpoint-v0.2.0
git switch -c sst/formal-clock-endpoint-v0.3.0
```

Extract the **contents** of this ZIP to the repository root, next to `lakefile.toml`. This adds `SSTFormal/ClockIntegral.lean` and a new `.cmd` file. It does not overwrite `Euler/`, `NavierStokes/`, the predecessor `SSTFormal/ClockEndpoint.lean`, or an existing root `VALIDATION.json`.

```powershell
.\run_sstformal_clockintegral_v0.3.0.cmd
$LASTEXITCODE
```

The script compiles the local Stage-A module to an importable `.olean`, then checks Stage B, stores output in `sstformal_clockintegral_v0.3.0_build.log`, and prints axiom lists. **A script exit code of zero is necessary; inspect warnings, all theorem axiom outputs, and the git diff before recording a local PASS.**

If `.olean` location differs in your Lake setup, adjust `-o` and the corresponding `LEAN_PATH`/Lake build location consistently. The patch deliberately does **not** run Comparator, edit the lakefile, or rebuild Mathlib.

## Mathematics

Let `q : ℝ → ℝ` be continuous, strictly positive *at every real time*, and let `T > 0`. Define

\[
\tau(t)=\int_0^t q(s)\,ds, \qquad \tau_* =\tau(T).
\]

The theorem chain is:

1. `clockPrimitive_hasDerivAt`: \(\tau'(t)=q(t)\), via the fundamental theorem of calculus.
2. `clockPrimitive_continuous`: continuous time primitive.
3. `clockPrimitive_strictMono`: \(\tau\) is strictly increasing since \(q>0\).
4. `clockEndpoint_pos`: \(\tau_*>0\) for \(T>0\).
5. `clockPrimitive_exists_preimage`: for \(0<\vartheta<\tau_*\), there is \(t\in(0,T)\) with \(\tau(t)=\vartheta\), by the intermediate value theorem.
6. `inverseClock_spec` and `inverseClock_clockPrimitive`: a noncomputable inverse exists **on the physical interval**; no global surjectivity is claimed.
7. `inverseClock_endpointCorrespondence`: both near-endpoint conditions of FV02-A follow from the integrated positive clock.
8. `unboundedNearLeft_iff_after_integrated_clock`: the real-valued endpoint-unboundedness equivalence follows by reusing FV02-A.

An analytic reference example is \(q(t) = (1+t^2)^{-1}\) on \(T=1\), with \(\tau(t)=\arctan t\), \(\tau_*=\pi/4\), and \(t(\tau)=\tan\tau\) on \((0,\pi/4)\). This example is explanatory and is **not** a separate Lean theorem in this release.

## Scientific scope and limitations

- This release uses **stronger assumptions** than the ultimate goal `q > 0` almost everywhere with only local \(L^1\) regularity. Relaxing those assumptions is future work; **do not mark the a.e. variant PASS**.
- The inverse is deliberately specified only for \(\tau\in(0,\tau_*)\); outside this interval its fallback value has no physical interpretation.
- A local scalar time-rate is not a proof of a global Euler time-foliation for a spatially dependent SST Swirl Clock field.
- The module does not yet convert `Euler.Solution`'s extended-nonnegative-real (`ENNReal`) \(C^1\)-norm limsup to the real-valued endpoint-unboundedness predicate (FV02-C).
- The module contains no kinetic or dynamical feedback. It cannot establish stability of finite-core knots or resolve Euler singularities.
- No SST canonical constants, electron inputs, Planck constants or quantum target values are used.

## Validation gate

After a successful local run, preserve commit SHA and SHA-256 hashes of the script, proof file, and log, and write a new versioned validation record. **Do not overwrite the predecessor's `VALIDATION.json`**. The archive includes `SSTFormal/VALIDATION_FV02B.json` initially set to `NOT_EXECUTED`.

Suggested commit:

```powershell
git add SSTFormal/ClockIntegral.lean SSTFormal/VALIDATION_FV02B.json `
  run_sstformal_clockintegral_v0.3.0.cmd README_FV02B_v0.3.0.md
git commit -m "Add SST-FV02 stage B integrated clock and inverse proofs"
```

## Main mathematical references

```latex
\bibitem{Buckingham1914}
E. Buckingham (1914).
On Physically Similar Systems; Illustrations of the Use of Dimensional Equations.
Physical Review 4, 345--376.
doi:10.1103/PhysRev.4.345

\bibitem{Mathlib2020}
The mathlib Community (2020).
The Lean Mathematical Library.
Proceedings of the 9th ACM SIGPLAN International Conference
on Certified Programs and Proofs, 367--381.
doi:10.1145/3372885.3373824
```
