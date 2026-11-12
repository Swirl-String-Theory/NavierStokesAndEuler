import Euler.PotentialFlow.Definitions

/-!
# Curl of a gradient vanishes

Under `ContDiff ℝ 2` regularity, mixed second partials commute, so
`∇ × (∇φ) = 0`.
-/

noncomputable section

open ContDiff InnerProductSpace
open scoped ContDiff

namespace Euler.PotentialFlow

theorem gradient_coordinate (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient φ x i = partialDerivative φ i x := by
  simpa only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, partialDerivative]
    using (inner_gradient_left (f := φ) (x := x) (y := EuclideanSpace.single i 1))

theorem partialDerivative_comm (φ : Space → ℝ) (hφ : ContDiff ℝ 2 φ)
    (i j : Fin 3) (x : Space) :
    partialDerivative (partialDerivative φ i) j x =
      partialDerivative (partialDerivative φ j) i x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have he (a b : Fin 3) :
      partialDerivative (partialDerivative φ a) b x =
        fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold partialDerivative
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he, he]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)).eq _ _

/-- Coordinate expression of `curl (∇φ)`. -/
theorem curl_potentialVelocity_apply (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    curl (potentialVelocity φ) x i =
      partialDerivative (fun y => potentialVelocity φ y (i + 2)) (i + 1) x -
        partialDerivative (fun y => potentialVelocity φ y (i + 1)) (i + 2) x := by
  simp only [curl, PiLp.toLp_apply]

theorem curl_potentialVelocity_apply' (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    curl (potentialVelocity φ) x i =
      partialDerivative (partialDerivative φ (i + 2)) (i + 1) x -
        partialDerivative (partialDerivative φ (i + 1)) (i + 2) x := by
  rw [curl_potentialVelocity_apply]
  simp only [potentialVelocity, gradient_coordinate]

/-- `∇ × ∇φ = 0` for twice continuously differentiable scalar potentials. -/
theorem curl_potentialVelocity (φ : Space → ℝ) (hφ : ContDiff ℝ 2 φ) (x : Space) :
    curl (potentialVelocity φ) x = 0 := by
  ext i
  rw [curl_potentialVelocity_apply', partialDerivative_comm φ hφ, sub_self, PiLp.zero_apply]

/-- Irrotationality of every sufficiently smooth potential velocity field. -/
theorem isIrrotational_potentialVelocity (φ : Space → ℝ) (hφ : ContDiff ℝ 2 φ) :
    IsIrrotationalOn Set.univ (potentialVelocity φ) := by
  intro x _
  exact curl_potentialVelocity φ hφ x

/-- Same identity under infinite smoothness. -/
theorem curl_potentialVelocity_of_smooth (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    curl (potentialVelocity φ) x = 0 :=
  curl_potentialVelocity φ (hφ.of_le (by simp)) x

end Euler.PotentialFlow
