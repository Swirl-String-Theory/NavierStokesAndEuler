import Euler.PotentialFlow.GradientCurl

/-!
# Incompressibility ↔ harmonicity for potential velocity

For `v = ∇φ` with sufficient smoothness,

```
∇ · v = Δφ
```

hence

```
∇ · v = 0  ↔  Δφ = 0.
```
-/

noncomputable section

open ContDiff InnerProductSpace Laplacian
open scoped ContDiff

namespace Euler.PotentialFlow

/-- Coordinate trace of a continuous endomorphism of `Space`. -/
def coordinateTrace (A : Space →L[ℝ] Space) : ℝ :=
  ∑ i : Fin 3, A (EuclideanSpace.single i 1) i

theorem coordinateTrace_eq_linearTrace (A : Space →L[ℝ] Space) :
    coordinateTrace A = LinearMap.trace ℝ Space A.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [coordinateTrace, Matrix.trace, LinearMap.toMatrix_apply]

theorem contDiff_partialDerivative (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (partialDerivative φ i) :=
  (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_gradient (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient φ) := by
  change ContDiff ℝ ∞ (fun x => (toDual ℝ Space).symm (fderiv ℝ φ x))
  exact (toDual ℝ Space).symm.contDiff.comp (hφ.fderiv_right (m := ∞) (by simp))

theorem fderiv_coordinate (v : Space → Space) (x : Space)
    (hv : DifferentiableAt ℝ v x) (i : Fin 3) (w : Space) :
    fderiv ℝ (fun y => v y i) x w = (fderiv ℝ v x w) i := by
  have he : HasFDerivAt (fun y => v y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ v x)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (v x) i).comp x hv.hasFDerivAt
  rw [he.fderiv]
  rfl

theorem divergence_eq_coordinate_sum (v : Space → Space) (x : Space) :
    divergence v x = ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i 1)) i := by
  change LinearMap.trace ℝ Space (fderiv ℝ v x).toLinearMap =
    ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i 1)) i
  rw [← coordinateTrace_eq_linearTrace]
  rfl

theorem laplacian_eq_coordinate_sum (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    Δ φ x = ∑ i : Fin 3, partialDerivative (partialDerivative φ i) i x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis φ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hdf : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, partialDerivative]
  change _ = (fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x)
    (EuclideanSpace.single i 1)
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

/-- `∇ · (∇φ) = Δφ`. -/
theorem divergence_potentialVelocity_eq_laplacian (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (x : Space) : divergence (potentialVelocity φ) x = Δ φ x := by
  have hg : ContDiff ℝ ∞ (potentialVelocity φ) := contDiff_gradient φ hφ
  rw [divergence_eq_coordinate_sum, laplacian_eq_coordinate_sum φ hφ x]
  apply Finset.sum_congr rfl
  intro i _
  have hdiff : DifferentiableAt ℝ (potentialVelocity φ) x :=
    (hg.differentiable (by simp)).differentiableAt
  rw [← fderiv_coordinate (potentialVelocity φ) x hdiff i]
  have heq : (fun y => potentialVelocity φ y i) = partialDerivative φ i :=
    funext fun y => by simp [potentialVelocity, gradient_coordinate]
  simp only [heq, partialDerivative]

/-- Incompressibility of a potential velocity field is equivalent to harmonicity. -/
theorem div_free_potentialVelocity_iff_harmonic (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (∀ x, divergence (potentialVelocity φ) x = 0) ↔ (∀ x, Δ φ x = 0) := by
  constructor
  · intro h x
    exact (divergence_potentialVelocity_eq_laplacian φ hφ x).symm.trans (h x)
  · intro h x
    exact (divergence_potentialVelocity_eq_laplacian φ hφ x).trans (h x)

/-- Pointwise form of the equivalence. -/
theorem div_free_potentialVelocity_iff_harmonic_at (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (x : Space) :
    divergence (potentialVelocity φ) x = 0 ↔ Δ φ x = 0 := by
  rw [divergence_potentialVelocity_eq_laplacian φ hφ x]

end Euler.PotentialFlow
