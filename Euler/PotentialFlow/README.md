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
| `Bernoulli.lean` | Convective identity; conditional + joint-`ContDiff` Bernoulli reduction |
| `ExteriorDomain.lean` | `D = ℝ³ \ K`, openness, exterior regularity packages |
| `Circulation.lean` | 2D vortex: curl-free, circulation `2π`, no global potential |
| `VortexCoreCoupling.lean` | Helmholtz/Hodge **reconstruction contract**; SST attachment strings |

## Changelog

### v0.1.1

- **A:** Proved `ContDiffOn ℝ ∞ vortexVelocity2D puncturedPlane` and
  `curl_free_vortexVelocity2D`. `local_irrotational_with_nonzero_circulation`
  is unconditional (no external curl hypothesis).
- **B:** Added `HasGlobalScalarPotential2D` and proved
  `not_hasGlobalScalarPotential2D_vortexVelocity2D` via FTC on the unit circle
  against circulation `2π`.
- **C:** Replaced vacuous `reconstruction : Prop := True` with a mandatory
  reconstruction identity; derived
  `helmholtzHodge_divergence_of_reconstruction`. Removed `True`-as-Prop
  `PotentialFlowNonClaims` (hygiene lives in module docs / README).
- **D:** Added `deriv_potentialVelocity_eq_gradient_deriv` and
  `bernoulli_reduction_of_joint_contDiff` (derives `hswap` from joint
  `ContDiff`). Conditional lemmas retained.

### v0.1.0

- Initial additive module family; planar circulation `2π`; conditional Bernoulli;
  Hodge interface placeholders.

## Proven theorems (selected)

- `curl_potentialVelocity` — curl of a gradient vanishes (`ContDiff ℝ 2`)
- `divergence_potentialVelocity_eq_laplacian` / `div_free_potentialVelocity_iff_harmonic`
- `convectiveAccel_potentialVelocity` — `(∇φ·∇)∇φ = ∇(½‖∇φ‖²)`
- `deriv_potentialVelocity_eq_gradient_deriv` — `∂ₜ∇φ = ∇∂ₜφ` under joint `C²`
- `bernoulli_reduction_of_joint_contDiff` — spatial constant `C(t)` from joint smoothness + momentum
- `exists_bernoulli_spatial_constant` / `bernoulli_reduction` — conditional bridge
- `contDiffOn_vortexVelocity2D` / `curl_free_vortexVelocity2D`
- `vortex_circulation_unitCircle` — unit-circle circulation equals `2π`
- `local_irrotational_with_nonzero_circulation` — unconditional coexistence
- `not_hasGlobalScalarPotential2D_vortexVelocity2D` — no global single-valued potential
- `helmholtzHodge_divergence_of_reconstruction` — div identity from reconstruction contract
- `coupling_exterior_irrotational` — coupling interface implies exterior irrotationality

## Local vs global potentials

`IsIrrotationalOn` / `HasGlobalScalarPotential` (3D) and `HasGlobalScalarPotential2D`
(2D) are separate predicates. The planar vortex is locally curl-free with
nonzero circulation `2π`, hence has **no** global single-valued scalar potential
on the punctured plane (`not_hasGlobalScalarPotential2D_vortexVelocity2D`).

## Open obligations

| ID | Status | Note |
|---|---|---|
| Knotted 3D exterior circulation / homology | `BLOCKED` | Needs de Rham / line-integral APIs (`openObligation_knottedExteriorCirculation`) |
| Full Hodge existence/uniqueness on exteriors | `UNRESOLVED` | Reconstruction contract only (`openObligation_hodgeDecomposition`) |
| Ruban Trefoil geometry adapter | deferred | Not implemented |
| Numerical validation paths | not executed | Documented attachment strings only |

## SST non-claims (documentation)

1. Potential flow does not replace internal vortex dynamics.
2. Irrotational exterior ≠ zero circulation.
3. Local potential ≠ globally single-valued.
4. Exterior structure ≠ Ruban Trefoil stability/persistence.

Frozen Framework v1.1.2 and SST-Workbench are **not** modified.

## Build

```bat
run_euler_potential_flow.cmd
```

or:

```bash
lake env lean Euler/PotentialFlow.lean
lake build Euler.PotentialFlow
```

Gate report: `VALIDATION_POTENTIAL_FLOW.json`.
