# SSTFormal ClockEndpoint v0.5.0 — FV02-C2

## Goal

Convert the `ENNUnboundedNearLeft` theorem proved in FV02-C1 into the literal
extended-nonnegative endpoint statement

```lean
Filter.limsup
  (fun τ : ℝ => ENNReal.ofReal (eulerC1RealProfile (inverseClock ... τ)))
  (𝓝[<] (clockPrimitive q EulerPacketInduction.lifespan.duration)) = ⊤
```

The added general lemma works for `f : ℝ → ENNReal` and does not require
continuity of `f`. We also show the unreparameterized Euler C¹ limsup.

## Prerequisites

- Checkout the **locally passed** `sst/formal-clock-euler-c1-v0.4.0`
  (reported commit `6be6f19`).
- Lean: `leanprover/lean4:v4.34.0-rc2`, unchanged mathlib/Lake dependencies.
- Required existing files: `ClockEndpoint.lean`, `ClockIntegral.lean`,
  `ClockEulerC1.lean`.
- Do not reset, clean, or modify those files.

## Installation (PowerShell)

```powershell
cd C:\workspace\projects\NavierStokesAndEuler
git switch sst/formal-clock-euler-c1-v0.4.0
git switch -c sst/formal-clock-euler-c1limsup-v0.5.0
# Extract the ZIP here; it adds SSTFormal/ClockEulerC1Limsup.lean
.\run_sstformal_clockeulerc1limsup_v0.5.0.cmd
```

Check the exit code **and** the emitted axiom lists. Report any Lean type
errors verbatim. No `sorry`, `admit`, or new axioms are intended.

## Scope and nonclaims

- `q` is a global scalar clock rate, everywhere continuous and positive.
- It is a **passive** time change; the Euler vector field is unchanged.
- This does not prove stable trefoils, prevent blowup, or derive a
  space-dependent clock foliation.
- Stage C1's identification of `eulerC1RealProfile` with the actual
  Euler comparator C¹ norm is reused; no new physical constants.
- `independent_assistant_execution` remains `false` until an actual
  independent Lean build is performed.

## Acceptance gates

1. Windows build exit code 0; all three `#print axioms` outputs allowed only.
2. No `sorryAx` and no Lean errors or warnings.
3. Existing FV02 A/B/C1 files unchanged from the last locally passed commit.
4. The validation artifact can be marked `PASS_LOCAL_LEAN_USER_REPORTED`
   only **after** a local successful run; starter ships `NOT_EXECUTED`.
