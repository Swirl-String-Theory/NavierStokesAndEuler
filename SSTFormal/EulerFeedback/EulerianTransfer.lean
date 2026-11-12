import SSTFormal.EulerFeedback.VorticityBound

/-!
# FV03-A — from material trajectories to an Eulerian pointwise bound

A material bound does not automatically become a bound on the full spatial
field. The flow map must COVER the physical domain and the field must equal
the transported vorticity on the corresponding trajectory. Those premises
are explicit below and are NOT consequences of the preceding ODE alone.

The eventual Euler-PDE bridge must prove these hypotheses for its own class
of smooth incompressible solutions and the entire pre-blowup interval.
-/

noncomputable section

open Set

namespace SSTFormal.EulerFeedback

/-- Transfer a uniform material bound to every spatial point, given
    surjective trajectory coverage and exact identification of transported
    vorticity with the Eulerian field. No hidden numerical assumptions. -/
theorem eulerian_norm_sq_bound_from_trajectory_coverage
    {Label Space E : Type*} [NormedAddCommGroup E]
    (T B : ℝ) (X : Label → ℝ → Space)
    (omega : Label → ℝ → E) (field : ℝ → Space → E)
    (hcover : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      ∃ a : Label, X a t = x)
    (hidentify : ∀ a t, t ∈ Ico (0 : ℝ) T →
      field t (X a t) = omega a t)
    (hbound : ∀ a t, t ∈ Ico (0 : ℝ) T →
      ‖omega a t‖ ^ 2 ≤ B)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    ‖field t x‖ ^ 2 ≤ B := by
  obtain ⟨a, hax⟩ := hcover t ht x
  rw [← hax, hidentify a t ht]
  exact hbound a t ht

/-- The analogous amplitude bound. In particular a uniform bound over
    initial labels gives a bound at all spatial points, WHEN coverage holds. -/
theorem eulerian_norm_bound_from_trajectory_coverage
    {Label Space E : Type*} [NormedAddCommGroup E]
    (T B : ℝ) (X : Label → ℝ → Space)
    (omega : Label → ℝ → E) (field : ℝ → Space → E)
    (hcover : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      ∃ a : Label, X a t = x)
    (hidentify : ∀ a t, t ∈ Ico (0 : ℝ) T →
      field t (X a t) = omega a t)
    (hbound : ∀ a t, t ∈ Ico (0 : ℝ) T →
      ‖omega a t‖ ≤ B)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    ‖field t x‖ ≤ B := by
  obtain ⟨a, hax⟩ := hcover t ht x
  rw [← hax, hidentify a t ht]
  exact hbound a t ht

end SSTFormal.EulerFeedback

#print axioms SSTFormal.EulerFeedback.eulerian_norm_sq_bound_from_trajectory_coverage
#print axioms SSTFormal.EulerFeedback.eulerian_norm_bound_from_trajectory_coverage
