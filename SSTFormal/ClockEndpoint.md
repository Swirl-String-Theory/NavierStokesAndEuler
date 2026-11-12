# SST-FV02 — Endpoint unboundedness with a passive time change

Status: **NOT EXECUTED**. Additive research starter, no claim of successful local Lean verification.

## Prerequisite

User-reported SST-FV01 local Lean PASS on `sst/formal-passive-clock-v0.1.0`, commit `f29de7a`. Build the same pinned Lean toolchain (v4.34.0-rc2) with Mathlib dependencies available.

## Install / run on Windows

Create a new local branch from the verified FV01 commit, then extract this zip **at the repository root** (beside `lakefile.toml`). No original `Euler/`, `NavierStokes/`, `SSTFormal/PassiveClock.lean`, or `ComparatorChallenges/` files are overwritten.

```powershell
git switch sst/formal-passive-clock-v0.1.0
git switch -c sst/formal-clock-endpoint-v0.2.0
.\run_sstformal_clockendpoint.cmd
```

The batch script calls `lake env lean SSTFormal\ClockEndpoint.lean`, writes `sstformal_clockendpoint_build.log`, checks the exit code, and prints axiom dependencies.

## Precise mathematical content

- `UnboundedNearLeft f T`: for every bound `M` and every lower cutoff `a<T`, some `t in (a,T)` has `f(t)>M`.
- `EndpointClockCorrespondence absoluteTime Tstar taustar`: two neighborhood-matching conditions. This is an **assumption**, not yet derived from a physical clock law.
- `unboundedNearLeft_iff_after_endpoint_clock`: a proof that endpoint unboundedness of a real scalar observable is unchanged by such an endpoint-matching time change.
- `endpoint_blowup_survives_passive_clock`: the direct implication.

## What is NOT proved

1. A positive clock rate `s(t)` alone is not a formal `EndpointClockCorrespondence`; its integral and inverse have not been constructed here.
2. No theorem directly converts `Euler.exists_compact_smooth_euler_singularity`'s `ENNReal`-valued `limsup` into `UnboundedNearLeft`.
3. No active Swirl Clock feedback law or altered Euler equation is justified.

Next work: prove the positive-rate clock integration lemma and the observable bridge. Freeze the verified FV01 commit as baseline.
