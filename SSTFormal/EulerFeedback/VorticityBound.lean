import SSTFormal.EulerFeedback.StretchingBound
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# FV03-A — vector vorticity and the Euler stretching rate

Conditional mathematical layer for the linear material-vorticity ODE
    omega'(t) = A(t) omega(t).
Here A is intended to be the velocity-gradient operator evaluated on an
actual material trajectory; this identification has to be proved in the
Euler PDE bridge, not assumed to follow from compilation alone.

The scalar sigma is the aligned stretch, defined by the identity
    <omega, A omega> = sigma * ||omega||^2.
This avoids dividing by zero vorticity. A primitive Phi'=sigma and
Phi(t)<=C imply ||omega(t)|| <= ||omega(0)|| * exp(C), 0<=t<T.

No assumption extends omega, A or Phi through the endpoint T.
-/

noncomputable section

open Set InnerProductSpace
open scoped Topology

namespace SSTFormal.EulerFeedback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A skew-adjoint linear map contributes no aligned stretching. -/
theorem skew_operator_has_zero_aligned_stretch
    (K : E →L[ℝ] E)
    (hK : ∀ x y : E, ⟪K x, y⟫_ℝ = -⟪x, K y⟫_ℝ)
    (w : E) : ⟪w, K w⟫_ℝ = 0 := by
  have h : ⟪w, K w⟫_ℝ = -⟪w, K w⟫_ℝ := by
    calc
      ⟪w, K w⟫_ℝ = ⟪K w, w⟫_ℝ := real_inner_comm _ _
      _ = -⟪w, K w⟫_ℝ := hK w w
  linarith

/-- The skew-adjoint part (local rigid rotation) does not enter the
    inner-product stretching observable. -/
theorem aligned_stretch_ignores_skew_part
    (S K : E →L[ℝ] E)
    (hK : ∀ x y : E, ⟪K x, y⟫_ℝ = -⟪x, K y⟫_ℝ)
    (w : E) :
    ⟪w, (S + K) w⟫_ℝ = ⟪w, S w⟫_ℝ := by
  calc
    ⟪w, (S + K) w⟫_ℝ = ⟪w, S w + K w⟫_ℝ := by
      simp [add_apply]
    _ = ⟪w, S w⟫_ℝ + ⟪w, K w⟫_ℝ := by
      rw [inner_add_right]
    _ = ⟪w, S w⟫_ℝ := by
      rw [skew_operator_has_zero_aligned_stretch K hK w]; ring

/-- Exact vorticity-energy derivative for a material stretching ODE.
    This is NOT an assertion that the Euler PDE hypotheses hold. -/
theorem vorticity_norm_sq_hasDerivAt
    (T : ℝ) (ω : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (hω : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt ω (A t (ω t)) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => ‖ω s‖ ^ 2)
      (2 * ⟪ω t, A t (ω t)⟫_ℝ) t := by
  exact (hω t ht).norm_sq

/-- The vector material law and actual aligned stretch provide the scalar
    ODE for squared vorticity. No division by ||omega|| is made. -/
theorem vorticity_norm_sq_scalar_law
    (T : ℝ) (ω : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (σ : ℝ → ℝ)
    (hω : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt ω (A t (ω t)) t)
    (halign : ∀ t ∈ Ioo (0 : ℝ) T,
      ⟪ω t, A t (ω t)⟫_ℝ = σ t * ‖ω t‖ ^ 2)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => ‖ω s‖ ^ 2)
      ((2 * σ t) * ‖ω t‖ ^ 2) t := by
  have h := vorticity_norm_sq_hasDerivAt T ω A hω t ht
  rw [halign t ht] at h
  convert h using 1; ring

/-- Core FV03-A result, with an arbitrary (possibly singular at T)
    aligned-stretch function sigma. The primitive Phi exists on [0,T)
    and is uniformly bounded ABOVE; no pointwise sigma bound is required. -/
theorem vorticity_norm_sq_bound_before_endpoint
    (T C : ℝ) (ω : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (σ Φ : ℝ → ℝ)
    (hωcont : ∀ t < T, ContinuousAt ω t)
    (hΦcont : ∀ t < T, ContinuousAt Φ t)
    (hω : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt ω (A t (ω t)) t)
    (halign : ∀ t ∈ Ioo (0 : ℝ) T,
      ⟪ω t, A t (ω t)⟫_ℝ = σ t * ‖ω t‖ ^ 2)
    (hΦ : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt Φ (σ t) t)
    (hΦ0 : Φ 0 = 0)
    (hcap : ∀ t ∈ Ico (0 : ℝ) T, Φ t ≤ C)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ‖ω t‖ ^ 2 ≤ ‖ω 0‖ ^ 2 * Real.exp (2 * C) := by
  let w : ℝ → ℝ := fun s => ‖ω s‖ ^ 2
  let I : ℝ → ℝ := fun s => 2 * Φ s
  let rate : ℝ → ℝ := fun s => 2 * σ s
  have hwcont : ∀ s < T, ContinuousAt w s := by
    intro s hs
    exact (hωcont s hs).norm.pow 2
  have hIcont : ∀ s < T, ContinuousAt I s := by
    intro s hs
    exact (hΦcont s hs).const_mul 2
  have hw : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt w (rate s * w s) s := by
    intro s hs
    exact vorticity_norm_sq_scalar_law T ω A σ hω halign s hs
  have hI : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt I (rate s) s := by
    intro s hs
    exact (hΦ s hs).const_mul 2
  have hI0 : I 0 = 0 := by simp [I, hΦ0]
  have hcapI : ∀ s ∈ Ico (0 : ℝ) T, I s ≤ 2 * C := by
    intro s hs
    exact mul_le_mul_of_nonneg_left (hcap s hs) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [w, I, rate] using
    scalar_stretching_upper_bound T w I rate hwcont hIcont hw hI hI0
      (sq_nonneg (‖ω 0‖)) (2 * C) hcapI t ht

/-- Convenient amplitude version: the bound exp(C), rather than exp(2C),
    applies to ||omega|| (not the squared norm). -/
theorem vorticity_norm_bound_before_endpoint
    (T C : ℝ) (ω : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (σ Φ : ℝ → ℝ)
    (hωcont : ∀ t < T, ContinuousAt ω t)
    (hΦcont : ∀ t < T, ContinuousAt Φ t)
    (hω : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt ω (A t (ω t)) t)
    (halign : ∀ t ∈ Ioo (0 : ℝ) T,
      ⟪ω t, A t (ω t)⟫_ℝ = σ t * ‖ω t‖ ^ 2)
    (hΦ : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt Φ (σ t) t)
    (hΦ0 : Φ 0 = 0)
    (hcap : ∀ t ∈ Ico (0 : ℝ) T, Φ t ≤ C)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ‖ω t‖ ≤ ‖ω 0‖ * Real.exp C := by
  have hsq := vorticity_norm_sq_bound_before_endpoint T C ω A σ Φ
    hωcont hΦcont hω halign hΦ hΦ0 hcap t ht
  have heq : Real.exp (2 * C) = (Real.exp C) ^ 2 := by
    rw [show (2 : ℝ) * C = C + C by ring, Real.exp_add]
    ring
  rw [heq] at hsq
  have hn : 0 ≤ ‖ω t‖ := norm_nonneg _
  have hbound : 0 ≤ ‖ω 0‖ * Real.exp C :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos C).le
  nlinarith [hsq]

end SSTFormal.EulerFeedback

#print axioms SSTFormal.EulerFeedback.skew_operator_has_zero_aligned_stretch
#print axioms SSTFormal.EulerFeedback.aligned_stretch_ignores_skew_part
#print axioms SSTFormal.EulerFeedback.vorticity_norm_sq_hasDerivAt
#print axioms SSTFormal.EulerFeedback.vorticity_norm_sq_scalar_law
#print axioms SSTFormal.EulerFeedback.vorticity_norm_sq_bound_before_endpoint
#print axioms SSTFormal.EulerFeedback.vorticity_norm_bound_before_endpoint
