import SSTFormal.EulerFeedback.PressureHessian
import Euler.FiniteIntervalFlow

/-!
SST-FV03-B3: material-flow coverage on every regular, finite horizon.

The flow and two-sided inverse below are CONSTRUCTED by the original Euler
formalization for a bounded, jointly continuous, uniformly Lipschitz field.
No surjectivity is assumed as an axiom or a new field hypothesis.

A single uniform Lipschitz constant for the entire half-open interval
[0,T*) is NOT asserted. The result may be used on each S<T* when its
own finite-horizon hypotheses are independently verified.
-/

noncomputable section

open Set
open scoped NNReal Topology BoundedContinuousFunction

namespace SSTFormal.EulerFeedback

/-- For a finite horizon the original flow-existence theorem gives
    a surjective material map (indeed a two-sided continuous inverse). -/
theorem finite_horizon_material_flow_covers_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (S : ℝ) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, E →ᵇ E)) (K : ℝ≥0)
    (hLip : ∀ t, LipschitzWith K (u t)) :
    ∃ X : ℝ → E → E,
      (∀ x, X 0 x = x) ∧
      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : E,
        ∃ a : E, X t a = x) ∧
      (∀ (t : Icc (0 : ℝ) S) (a : E),
        HasDerivAt (fun r => X r a) (u t (X t a)) t) := by
  obtain ⟨X,Y,hXzero,_hYzero,_hXcont,_hYcont,_hYX,hXY,hODE,_hdisp⟩ :=
    EulerBoundedLipschitzFlow.exists_flow_and_inverse S hS u K hLip
  refine ⟨X, hXzero, ?_, hODE⟩
  intro t ht x
  exact ⟨Y t x, hXY t x⟩

/-- Material-to-Eulerian bound with coverage now obtained from the
    constructed flow, not assumed. Identification and material magnitude
    bounds remain the substantive physical hypotheses. -/
theorem finite_horizon_material_bound_implies_eulerian_bound
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup V]
    (S B : ℝ) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, E →ᵇ E)) (K : ℝ≥0)
    (hLip : ∀ t, LipschitzWith K (u t)) :
    ∃ X : E → ℝ → E,
      ∀ (omega : E → ℝ → V) (field : ℝ → E → V),
        (∀ a t, t ∈ Ico (0 : ℝ) S →
          field t (X a t) = omega a t) →
        (∀ a t, t ∈ Ico (0 : ℝ) S → ‖omega a t‖ ≤ B) →
        ∀ t ∈ Ico (0 : ℝ) S, ∀ x, ‖field t x‖ ≤ B := by
  obtain ⟨X,_hX0,hcover,_hODE⟩ :=
    finite_horizon_material_flow_covers_space S hS u K hLip
  refine ⟨fun a t => X t a, ?_⟩
  intro omega field hidentify hbound t ht x
  apply eulerian_norm_bound_from_trajectory_coverage
    S B (fun a r => X r a) omega field _ hidentify hbound t ht x
  intro r hr y
  exact hcover r hr y

end SSTFormal.EulerFeedback

#print axioms SSTFormal.EulerFeedback.finite_horizon_material_flow_covers_space
#print axioms SSTFormal.EulerFeedback.finite_horizon_material_bound_implies_eulerian_bound
