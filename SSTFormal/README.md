# SST Formal Verification — SST-FV01 (starter v0.1.0)

## Scope

This folder adds a small SST-specific formal proof layer to the forked
`NavierStokesAndEuler` repository. **Do not replace or edit the upstream
`Euler/`, `NavierStokes/` or `ComparatorChallenges/` modules.**

`PassiveClock.lean` proves:

1. A passive clock extension entails an underlying global Euler solution.
2. Consequently, some smooth compactly admissible Euler initial data admit
   no global Euler solution decorated with a passive clock.
3. A surjective change of time parameter preserves unboundedness of a
   real-valued observable over the entire parameter domain.

All three are **conditional / logical results**. They do not establish
active feedback, dynamical regularization, trefoil stability, a clock
law from Euler, or equivalence of endpoint limsups.

## How to install and test

1. Use the existing local clone, with Lean 4.34.0-rc2 and the already
   working `lake build`/Euler Comparator environment.
2. Create a separate branch from the currently verified commit:

   `git switch -c sst/formal-passive-clock-v0.1.0`

3. Copy the folder `SSTFormal/` and `run_sstformal_passiveclock.cmd` to the
   **root** of that clone (beside `lakefile.toml`).
4. Run in `cmd.exe` or PowerShell:

   `run_sstformal_passiveclock.cmd`

   Equivalent manual command:

   `lake env lean SSTFormal/PassiveClock.lean`

5. Only after a local exit code 0 and explicit `#print axioms` inspection
   should the new theorem be recorded as `PASS_LOCAL_LEAN`.
6. Commit the change. Preserve the original Euler Comparator as an
   independent upstream gate; the new SST theorem is not covered by
   the existing `ComparatorChallenges/Euler.json`.

## Important nuance

`PassiveClockGlobal` *includes* the unchanged Euler solution as a
requirement. The first proof is therefore intentionally an elementary
inheritance theorem, not an independently discovered physics result.
It identifies the logical limitation of a passive clock, nothing more.

The follow-up theorem will require a regular, monotone, cofinal mapping
of the finite Euler time interval to operational time to formalize
endpoint singularity under a genuine (possibly trajectory-dependent)
Swirl Clock law.

## Validation status

- Upstream Euler Comparator: user-reported PASS (Lean + nanoda, axioms OK),
  `landrun` sandbox NOT_EXECUTED on Windows.
- New SST-FV01: **NOT_EXECUTED** (authoring here is not local Lean testing).
- No parameter fitting, canonical SST constants, numerical backends,
  or experimental comparisons are used in this formal test.
