import Euler.PotentialFlow.ExteriorDomain

/-!
# Local irrotationality versus global circulation

Local irrotationality does not imply vanishing circulation, nor a single-valued
global scalar potential. This module records a checkable 2D witness and marks
general 3D knotted exteriors as blocked.
-/

noncomputable section

open Classical ContDiff Set Real MeasureTheory
open scoped Real Topology ContDiff

namespace Euler.PotentialFlow

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def puncturedPlane : Set Plane := {x : Plane | x ≠ 0}

theorem isOpen_puncturedPlane : IsOpen puncturedPlane := isOpen_ne

def vortexVelocity2D (x : Plane) : Plane :=
  let r2 := x 0 ^ 2 + x 1 ^ 2
  WithLp.toLp 2 ![(-x 1) / r2, x 0 / r2]

def unitCircle (θ : ℝ) : Plane := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

def unitCircleDeriv (θ : ℝ) : Plane := WithLp.toLp 2 ![(-Real.sin θ), Real.cos θ]

theorem unitCircle_ne_zero (θ : ℝ) : unitCircle θ ≠ 0 := by
  intro h
  have hc : Real.cos θ = 0 := by
    simpa [unitCircle] using congrArg (fun z : Plane => (z 0 : ℝ)) h
  have hs : Real.sin θ = 0 := by
    simpa [unitCircle] using congrArg (fun z : Plane => (z 1 : ℝ)) h
  have := Real.cos_sq_add_sin_sq θ
  simp [hc, hs] at this

def circulationIntegrand (θ : ℝ) : ℝ :=
  let v := vortexVelocity2D (unitCircle θ)
  let w := unitCircleDeriv θ
  v 0 * w 0 + v 1 * w 1

theorem circulationIntegrand_eq_one (θ : ℝ) : circulationIntegrand θ = 1 := by
  have hr : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  simp [circulationIntegrand, vortexVelocity2D, unitCircle, unitCircleDeriv, hr]
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem integral_one_Icc_zero_two_pi :
    ∫ _θ in Icc (0 : ℝ) (2 * Real.pi), (1 : ℝ) = 2 * Real.pi := by
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  simp [integral_const, Measure.real, Real.volume_Icc, hπ, sub_zero, smul_eq_mul]

theorem vortex_circulation_unitCircle :
    ∫ θ in Icc (0 : ℝ) (2 * Real.pi), circulationIntegrand θ = 2 * Real.pi := by
  have h1 : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), circulationIntegrand θ = 1 := fun _ _ =>
    circulationIntegrand_eq_one _
  rw [setIntegral_congr_fun measurableSet_Icc h1]
  exact integral_one_Icc_zero_two_pi

theorem vortex_circulation_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by
  positivity

structure PlanarVortexIrrotationalHypothesis : Prop where
  smooth_on_punctured : ContDiffOn ℝ ∞ vortexVelocity2D puncturedPlane
  curl_free :
    ∀ x ∈ puncturedPlane,
      fderiv ℝ (fun y => vortexVelocity2D y 1) x (EuclideanSpace.single 0 1) -
        fderiv ℝ (fun y => vortexVelocity2D y 0) x (EuclideanSpace.single 1 1) = 0

theorem local_irrotational_with_nonzero_circulation
    (h : PlanarVortexIrrotationalHypothesis) :
    (∀ x ∈ puncturedPlane,
        fderiv ℝ (fun y => vortexVelocity2D y 1) x (EuclideanSpace.single 0 1) -
          fderiv ℝ (fun y => vortexVelocity2D y 0) x (EuclideanSpace.single 1 1) = 0) ∧
      (∫ θ in Icc (0 : ℝ) (2 * Real.pi), circulationIntegrand θ = 2 * Real.pi) ∧
      ((2 * Real.pi : ℝ) ≠ 0) :=
  ⟨h.curl_free, vortex_circulation_unitCircle, vortex_circulation_ne_zero⟩

def openObligation_knottedExteriorCirculation : String :=
  "BLOCKED: general 3D knotted-exterior circulation vs global scalar potential \
requires de Rham / homology infrastructure beyond the present Mathlib surface."

theorem circulation_witness_nonzero : ∃ Γ : ℝ, Γ ≠ 0 ∧ Γ = 2 * Real.pi :=
  ⟨2 * Real.pi, vortex_circulation_ne_zero, rfl⟩

end Euler.PotentialFlow
