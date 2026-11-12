import SSTFormal.EulerFeedback.PDEtoODE
import Mathlib.Analysis.Normed.Operator.Basic

/-!
SST-FV03-B2: the pressure Hessian and material gradient Riccati identity.

For a sufficiently smooth incompressible Euler solution, along a material
path the velocity gradient A satisfies A' = - A*A - H, where H=Hess p.
Here hGradientPDE denotes the genuine spatial derivative of Euler momentum
and its time-space chain rule. It is still an explicit obligation.

No bound on cumulative aligned stretching is deduced from a bound on H
alone. A pressure Hessian can have either sign; this module MUST NOT be
interpreted as closing the non-circular stabilization gate.
-/

noncomputable section

open InnerProductSpace

namespace SSTFormal.EulerFeedback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Velocity-gradient material Riccati right-hand side. -/
def gradientRiccatiRhs (A H : E →L[ℝ] E) : E →L[ℝ] E :=
  -(A.comp A) - H

/-- Exact operator-norm estimate; no favorable sign is assumed for H. -/
theorem gradient_riccati_rhs_norm_le
    (A H : E →L[ℝ] E) :
    ‖gradientRiccatiRhs A H‖ ≤ ‖A‖ ^ 2 + ‖H‖ := by
  unfold gradientRiccatiRhs
  calc
    ‖-(A.comp A) - H‖ ≤ ‖-(A.comp A)‖ + ‖H‖ := norm_sub_le _ _
    _ = ‖A.comp A‖ + ‖H‖ := by rw [norm_neg]
    _ ≤ (‖A‖ * ‖A‖) + ‖H‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le A A) le_rfl
    _ = ‖A‖ ^ 2 + ‖H‖ := by ring

/-- The pressure Hessian is exactly the missing forcing in the gradient
    Riccati relation; a bound on A or on its rate is NOT inferred. -/
theorem pressure_hessian_balance_at_time
    (A H dA : E →L[ℝ] E)
    (hRiccati : dA = gradientRiccatiRhs A H) :
    dA + (A.comp A) + H = 0 := by
  rw [hRiccati]
  unfold gradientRiccatiRhs
  abel

/-- A conditional derivative bound for the material gradient; the actual
    Euler spatial-differentiation step is the named premise hGradientPDE. -/
theorem material_gradient_derivative_norm_le
    (A H : ℝ → E →L[ℝ] E) (t : ℝ)
    (hGradientPDE : HasDerivAt A (gradientRiccatiRhs (A t) (H t)) t) :
    ‖deriv A t‖ ≤ ‖A t‖ ^ 2 + ‖H t‖ := by
  rw [hGradientPDE.deriv]
  exact gradient_riccati_rhs_norm_le (A t) (H t)

/-- Algebraic expansion with A=S+W. If S is symmetric, W skew,
    and H symmetric, this separates the candidate strain/rotation terms.
    Symmetry and the corresponding dynamical projection are not asserted. -/
theorem riccati_strain_rotation_decomposition
    (S W H : E →L[ℝ] E) :
    gradientRiccatiRhs (S + W) H =
      -(S.comp S + S.comp W + W.comp S + W.comp W) - H := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [gradientRiccatiRhs, sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
    add_apply, map_add]
  abel

/-- The antisymmetric part of the velocity gradient has no direct
    aligned stretching contribution. The exact skew identity was
    separately established in FV03-A. -/
theorem pressure_strain_alignment_of_skew_decomposition
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S K : F →L[ℝ] F)
    (hskew : ∀ x y : F, ⟪K x, y⟫_ℝ = -⟪x, K y⟫_ℝ)
    (w : F) :
    ⟪w, (S + K) w⟫_ℝ = ⟪w, S w⟫_ℝ :=
  -- Fresh type variable avoids NormedSpace/InnerProductSpace instance diamond
  -- with the section-level `[NormedSpace ℝ E]` used by earlier theorems.
  aligned_stretch_ignores_skew_part S K hskew w

end SSTFormal.EulerFeedback

#print axioms SSTFormal.EulerFeedback.gradient_riccati_rhs_norm_le
#print axioms SSTFormal.EulerFeedback.pressure_hessian_balance_at_time
#print axioms SSTFormal.EulerFeedback.material_gradient_derivative_norm_le
#print axioms SSTFormal.EulerFeedback.riccati_strain_rotation_decomposition
#print axioms SSTFormal.EulerFeedback.pressure_strain_alignment_of_skew_decomposition
