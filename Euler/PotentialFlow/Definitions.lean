import Mathlib

/-!
# Scalar velocity potential for incompressible Euler

This module introduces **scalar** potential flow `v = ∇φ`.

It is intentionally distinct from the existing curl-gauge constructions in
`Euler.BaseEulerDatum` / `Euler.BaseEulerGevrey`, where a field named
`potential` / `vectorPotential` produces velocity via `v = curl A`.

```
scalar potential flow:   v = ∇φ
vector / Coulomb gauge:  v = ∇ × A
```

These are different gauges. Potential flow is a special class of
incompressible Euler solutions (irrotational), not a replacement for the
existing singularity theory.

The predicates `IsIrrotationalOn` and `HasGlobalScalarPotential` are kept
separate on purpose: local irrotationality does not imply a single-valued
global potential on multiply connected exterior domains. See
`Circulation.lean` for a concrete 2D model.
-/

noncomputable section

open ContDiff InnerProductSpace Set
open scoped ContDiff Topology

namespace Euler.PotentialFlow

/-- Ambient Euclidean 3-space, matching the rest of the Euler library. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Positive constant fluid mass density `ρ_f`. -/
structure FluidDensity where
  /-- Mass density. -/
  ρ : ℝ
  /-- Strict positivity. -/
  pos : 0 < ρ

/-- Divergence as the trace of the Fréchet derivative. -/
def divergence (v : Space → Space) (x : Space) : ℝ :=
  (fderiv ℝ v x).trace ℝ Space

/-- Coordinate partial derivative `∂ᵢ f`. -/
def partialDerivative (f : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- Classical curl of a vector field on `ℝ³`, with cyclic `Fin 3` indices. -/
def curl (v : Space → Space) (x : Space) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    partialDerivative (fun y => v y (i + 2)) (i + 1) x -
      partialDerivative (fun y => v y (i + 1)) (i + 2) x)

/-- Alias emphasizing the vorticity interpretation `ω = ∇ × v`. -/
abbrev vorticity (v : Space → Space) : Space → Space := curl v

/-- Euclidean cross product on `Space`, via Mathlib's `crossProduct`. -/
def cross (a b : Space) : Space :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

/--
Scalar velocity potential regularity: the potential is jointly smooth in
time and space on an open spacetime domain.
-/
structure ScalarPotentialRegularity (Ω : Set (ℝ × Space)) (φ : ℝ → Space → ℝ) : Prop where
  open_domain : IsOpen Ω
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × Space => φ p.1 p.2) Ω

/-- Instantaneous spatial regularity of a scalar potential at fixed time. -/
structure SpatialPotentialRegularity (D : Set Space) (φ : Space → ℝ) : Prop where
  open_domain : IsOpen D
  smooth : ContDiffOn ℝ ∞ φ D

/-- Velocity reconstructed from a scalar potential: `v := ∇φ`. -/
def potentialVelocity (φ : Space → ℝ) : Space → Space :=
  gradient φ

/-- Time-dependent potential velocity `v(t,x) = ∇_x φ(t,x)`. -/
def potentialVelocityAt (φ : ℝ → Space → ℝ) (t : ℝ) : Space → Space :=
  potentialVelocity (φ t)

/-- Pointwise convective acceleration `(v·∇)v`. -/
def convectiveAccel (v : Space → Space) (x : Space) : Space :=
  fderiv ℝ v x (v x)

/--
Incompressible Euler residual for a velocity/pressure pair with constant
density `ρ`, without external force:

`∂ₜv + (v·∇)v + (1/ρ) ∇p = 0` and `∇·v = 0`.
-/
structure IncompressibleEulerOn (D : Set Space) (I : Set ℝ)
    (ρ : FluidDensity) (v : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  open_space : IsOpen D
  open_time : IsOpen I
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => v q.1 q.2) (I ×ˢ D)
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2) (I ×ˢ D)
  div_free : ∀ t ∈ I, ∀ x ∈ D, divergence (v t) x = 0
  momentum : ∀ t ∈ I, ∀ x ∈ D,
    deriv (fun s => v s x) t + convectiveAccel (v t) x =
      -(1 / ρ.ρ) • gradient (p t) x

/-- Potential-flow specialization: velocity is exactly the spatial gradient of `φ`. -/
structure PotentialFlowOn (D : Set Space) (I : Set ℝ)
    (ρ : FluidDensity) (φ : ℝ → Space → ℝ) (p : ℝ → Space → ℝ) : Prop where
  potential_reg : ScalarPotentialRegularity (I ×ˢ D) φ
  euler : IncompressibleEulerOn D I ρ (fun t => potentialVelocityAt φ t) p

/-- Local irrotationality: vorticity vanishes on the spatial domain. -/
def IsIrrotationalOn (D : Set Space) (v : Space → Space) : Prop :=
  ∀ x ∈ D, curl v x = 0

/-- Global single-valued scalar potential representation on `D`. -/
def HasGlobalScalarPotential (D : Set Space) (v : Space → Space) : Prop :=
  ∃ φ : Space → ℝ, ContDiffOn ℝ ∞ φ D ∧ ∀ x ∈ D, v x = potentialVelocity φ x

@[simp] theorem potentialVelocity_apply (φ : Space → ℝ) (x : Space) :
    potentialVelocity φ x = gradient φ x := rfl

theorem FluidDensity.ne_zero (ρ : FluidDensity) : ρ.ρ ≠ 0 :=
  ne_of_gt ρ.pos

theorem FluidDensity.inv_ρ_pos (ρ : FluidDensity) : 0 < ρ.ρ⁻¹ :=
  inv_pos.mpr ρ.pos

end Euler.PotentialFlow
