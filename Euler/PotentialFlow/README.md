# Euler Potential Flow

Additive Lean 4 formalization of **scalar** potential flow as an irrotational
subclass of incompressible Euler, with an honest treatment of circulation on
multiply connected exterior domains.

## Gauge distinction (critical)

| Concept | Formula | Location |
|---|---|---|
| Scalar velocity potential (this module) | `v = ∇φ` | `Euler.PotentialFlow.potentialVelocity` |
| Existing curl / vector gauge | `v = ∇ × A` | `Euler.BaseEulerDatum.potential`, `vectorPotential` |

The existing BaseEuler `potential` is **not** a scalar speed potential. Public
APIs there were left unchanged.

## Toolchain

- Lean: `4.34.0-rc2` (`lean-toolchain`)
- Mathlib / Comparator: `v4.34.0-rc2` (`lakefile.toml`)
- Branch: `feature/euler-potential-flow`
- Lake discovery: `Euler.+` glob (no lakefile edit)

## Module map

| File | Role |
|---|---|
| `Definitions.lean` | Density, `potentialVelocity`, Euler/potential structures, local vs global predicates |
| `GradientCurl.lean` | `∇ × ∇φ = 0` under `ContDiff ℝ 2` |
| `Laplace.lean` | `∇ · ∇φ = Δφ`, hence incompressibility ↔ harmonicity |
| `Bernoulli.lean` | Convective identity for potential velocity; Bernoulli spatial constancy |
| `ExteriorDomain.lean` | `D = ℝ³ \ K`, openness, exterior regularity packages |
| `Circulation.lean` | 2D potential-vortex circulation `= 2π`; 3D knotted case `BLOCKED` |
| `VortexCoreCoupling.lean` | Helmholtz/Hodge **interface** only; SST attachment strings |

## Proven theorems (selected)

- `curl_potentialVelocity` — curl of a gradient vanishes (`ContDiff ℝ 2`)
- `divergence_potentialVelocity_eq_laplacian` / `div_free_potentialVelocity_iff_harmonic`
- `convectiveAccel_potentialVelocity` — `(∇φ·∇)∇φ = ∇(½‖∇φ‖²)`
- `exists_bernoulli_spatial_constant` / `bernoulli_reduction` — spatial constant `C(t)` on open preconnected domains when `∇Bernoulli = 0`
- `gradient_bernoulli_eq_zero_of_euler` — conditional bridge under explicit swap + momentum hypotheses
- `vortex_circulation_unitCircle` — unit-circle circulation equals `2π`
- `coupling_exterior_irrotational` — coupling interface implies exterior irrotationality

## Explicit hypotheses

- Bernoulli global constancy requires: open + preconnected domain, differentiability of the Bernoulli function, vanishing spatial gradient (or Euler momentum + `∂t`/`∇` commutation + Bernoulli gradient expansion).
- `C(t)` is **not** normalized to zero.
- Planar vortex irrotationality off the origin is packaged as `PlanarVortexIrrotationalHypothesis` (classical identity kept as an interface hypothesis).

## Local vs global potentials

`IsIrrotationalOn` and `HasGlobalScalarPotential` are separate predicates.
The planar vortex has nonzero circulation `2π` around the unit circle, so a
single-valued global scalar potential cannot exist on the punctured plane in
the usual sense. This refuses the false claim that every locally irrotational
exterior field has a global scalar potential.

## Open obligations

| ID | Status | Note |
|---|---|---|
| Knotted 3D exterior circulation / homology | `BLOCKED` | Needs de Rham / line-integral APIs beyond current Mathlib surface (`openObligation_knottedExteriorCirculation`) |
| Full Hodge decomposition on exteriors | `UNRESOLVED` | Interface only (`openObligation_hodgeDecomposition`) |
| Ruban Trefoil geometry adapter | deferred | Not implemented in this phase |
| Numerical validation paths | not executed | Documented attachment strings only |

## SST non-claims

1. Potential flow does not replace internal vortex dynamics.
2. Irrotational exterior ≠ zero circulation.
3. Local potential ≠ globally single-valued.
4. Exterior structure ≠ Ruban Trefoil stability/persistence.

Frozen Framework v1.1.2 and SST-Workbench are **not** modified.

## Literature (classical)

- Batchelor, *An Introduction to Fluid Dynamics* (potential flow, Bernoulli).
- Landau & Lifshitz, *Fluid Mechanics* (irrotational flow).
- Helmholtz / Hodge decompositions: standard vector-calculus and geometric analysis references; not claimed as proved here beyond the interface.

## Build

```bat
run_euler_potential_flow.cmd
```

or incrementally:

```bash
lake env lean Euler/PotentialFlow/Definitions.lean
lake env lean Euler/PotentialFlow/GradientCurl.lean
lake env lean Euler/PotentialFlow/Laplace.lean
lake env lean Euler/PotentialFlow/Bernoulli.lean
lake env lean Euler/PotentialFlow.lean
lake build
```

Gate report: `VALIDATION_POTENTIAL_FLOW.json`.
