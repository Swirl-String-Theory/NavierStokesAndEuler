import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# SST-FV03-A v0.1.0 — conditional vortex-stretching bound

This is a mathematically conditional result, not a proof that Euler's own
pressure Hessian, a Ruban trefoil, or a vortex lattice satisfies the condition.

All results live on the HALF-OPEN physical interval [0,T). They do NOT assume
regularity of a velocity/vorticity field at the possibly singular endpoint T.

Assume w' = sigma*w and an accumulated stretching primitive I' = sigma,
I(0)=0. Then w(t)=w(0)*exp(I(t)) for 0 <= t < T. If I(t)<=C,
and w(0)>=0, then w(t)<=w(0)*exp(C).

For Euler, w can be squared vorticity and the rate can be twice the
orientation-aligned stretching. The actual Euler material-derivative identity
and trajectory coverage remain prerequisites, NOT established by this file.

No physical/SST constants, new axioms, or `sorry` declarations.
-/

noncomputable section

open Set InnerProductSpace
open scoped Topology

namespace SSTFormal.EulerFeedback

/-- The integrating-factor quantity associated with a scalar stretching law. -/
def weightedInvariant (w I : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t * Real.exp (-I t)

/-- The integrating factor has zero derivative at every interior time. -/
theorem weightedInvariant_hasDerivAt_zero
    (T : ℝ) (w I σ : ℝ → ℝ)
    (hw : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt w (σ t * w t) t)
    (hI : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt I (σ t) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (weightedInvariant w I) 0 t := by
  -- Prefer pointwise `Real.exp` over `Pi.mul`/`NormedSpace.exp` forms
  -- so the integrating factor matches `weightedInvariant` definitionally.
  have hexp : HasDerivAt (fun s => Real.exp (-I s)) (Real.exp (-I t) * -(σ t)) t :=
    (hI t ht).neg.exp
  have hprod := (hw t ht).mul hexp
  have hzero :
      σ t * w t * Real.exp (-I t) +
        w t * (Real.exp (-I t) * -(σ t)) = 0 := by
    ring
  exact hprod.congr_deriv hzero

/-- Continuity only BEFORE T, not at T, is required. This avoids building
    a fictitious smooth Euler extension through a potential blowup. -/
theorem weightedInvariant_constant_before_endpoint
    (T : ℝ) (w I σ : ℝ → ℝ)
    (hwcont : ∀ t < T, ContinuousAt w t)
    (hIcont : ∀ t < T, ContinuousAt I t)
    (hw : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt w (σ t * w t) t)
    (hI : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt I (σ t) t)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    weightedInvariant w I t = weightedInvariant w I 0 := by
  let g := weightedInvariant w I
  have hgc : ContinuousOn g (Icc (0 : ℝ) t) := by
    intro x hx
    have hxT : x < T := lt_of_le_of_lt hx.2 ht.2
    have hcont : ContinuousAt g x := by
      refine ContinuousAt.mul (hwcont x hxT) ?_
      exact Real.continuous_exp.continuousAt.comp (ContinuousAt.neg (hIcont x hxT))
    exact hcont.continuousWithinAt
  have hgd : ∀ x ∈ interior (Icc (0 : ℝ) t),
      HasDerivWithinAt g 0 (interior (Icc (0 : ℝ) t)) x := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) t := by
      simpa only [interior_Icc] using hx
    have hxT : x ∈ Ioo (0 : ℝ) T := ⟨hx'.1, hx'.2.trans ht.2⟩
    exact (weightedInvariant_hasDerivAt_zero T w I σ hw hI x hxT).hasDerivWithinAt
  have hm : MonotoneOn g (Icc (0 : ℝ) t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hgc hgd
      (fun _ _ => le_rfl)
  have ha : AntitoneOn g (Icc (0 : ℝ) t) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hgc hgd
      (fun _ _ => le_rfl)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  have htime : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_rfl⟩
  exact le_antisymm (ha h0 htime ht.1) (hm h0 htime ht.1)

/-- Non-vacuous finite-time stretching identity: NO endpoint continuity. -/
theorem scalar_stretching_identity
    (T : ℝ) (w I σ : ℝ → ℝ)
    (hwcont : ∀ t < T, ContinuousAt w t)
    (hIcont : ∀ t < T, ContinuousAt I t)
    (hw : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt w (σ t * w t) t)
    (hI : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt I (σ t) t)
    (hI0 : I 0 = 0)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    w t = w 0 * Real.exp (I t) := by
  have hconst := weightedInvariant_constant_before_endpoint T w I σ
    hwcont hIcont hw hI t ht
  have hfactor : w t * Real.exp (-I t) = w 0 := by
    simpa [weightedInvariant, hI0] using hconst
  calc
    w t = (w t * Real.exp (-I t)) * Real.exp (I t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = w 0 * Real.exp (I t) := by rw [hfactor]

/-- A uniform upper bound on *integrated stretching* gives a uniform
    upper bound on the nonnegative scalar amplitude for all t<T. -/
theorem scalar_stretching_upper_bound
    (T : ℝ) (w I σ : ℝ → ℝ)
    (hwcont : ∀ t < T, ContinuousAt w t)
    (hIcont : ∀ t < T, ContinuousAt I t)
    (hw : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt w (σ t * w t) t)
    (hI : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt I (σ t) t)
    (hI0 : I 0 = 0)
    (hw0 : 0 ≤ w 0)
    (C : ℝ)
    (hcap : ∀ t ∈ Ico (0 : ℝ) T, I t ≤ C)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    w t ≤ w 0 * Real.exp C := by
  rw [scalar_stretching_identity T w I σ hwcont hIcont hw hI hI0 t ht]
  exact mul_le_mul_of_nonneg_left (Real.exp_monotone (hcap t ht)) hw0

/-- Pointwise-to-uniform bound over arbitrary material labels, with no
    assumption that any finite-time singularity is already ruled out. -/
theorem uniform_material_stretching_bound
    {Label : Type*} (T C W₀ : ℝ)
    (w I σ : Label → ℝ → ℝ)
    (hwcont : ∀ a t, t < T → ContinuousAt (w a) t)
    (hIcont : ∀ a t, t < T → ContinuousAt (I a) t)
    (hw : ∀ a t, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (w a) (σ a t * w a t) t)
    (hI : ∀ a t, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (I a) (σ a t) t)
    (hI0 : ∀ a, I a 0 = 0)
    (hw0 : ∀ a, 0 ≤ w a 0)
    (hinit : ∀ a, w a 0 ≤ W₀)
    (hcap : ∀ a t, t ∈ Ico (0 : ℝ) T → I a t ≤ C)
    (a : Label) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    w a t ≤ W₀ * Real.exp C := by
  calc
    w a t ≤ w a 0 * Real.exp C :=
      scalar_stretching_upper_bound T (w a) (I a) (σ a)
        (hwcont a) (hIcont a) (fun s hs => hw a s hs)
        (fun s hs => hI a s hs) (hI0 a) (hw0 a) C
        (fun s hs => hcap a s hs) t ht
    _ ≤ W₀ * Real.exp C :=
      mul_le_mul_of_nonneg_right (hinit a) (Real.exp_pos C).le

end SSTFormal.EulerFeedback

#print axioms SSTFormal.EulerFeedback.weightedInvariant_hasDerivAt_zero
#print axioms SSTFormal.EulerFeedback.weightedInvariant_constant_before_endpoint
#print axioms SSTFormal.EulerFeedback.scalar_stretching_identity
#print axioms SSTFormal.EulerFeedback.scalar_stretching_upper_bound
#print axioms SSTFormal.EulerFeedback.uniform_material_stretching_bound
