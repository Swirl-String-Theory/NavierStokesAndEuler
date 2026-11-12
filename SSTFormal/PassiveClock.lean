import Euler.Solution

/-!
# SST-FV01: Passive Swirl Clock and Euler breakdown

This file is an additive SST-specific proof layer; it does not modify
OpenAI's original Euler/ or ComparatorChallenges/ modules.

Scope: A passive local clock is an additional scalar field, bounded
strictly between zero and one on nonnegative absolute times. The
original incompressible Euler velocity and pressure still satisfy the
unchanged Euler equation. This is NOT a proof about active feedback.

No SST canonical constants, quantum constants, or experimental targets
occur in the assumptions.
-/

namespace SSTFormal

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A global smooth unforced Euler solution with a passive local clock.
    The clock does not enter the Euler momentum or incompressibility equations. -/
def PassiveClockGlobal (u₀ : Space → Space) : Prop :=
  ∃ (v : Space → ℝ → Space) (p : Space → ℝ → ℝ)
    (clockRate : Space → ℝ → ℝ),
    Euler.EulerExistenceAndSmoothnessR3 u₀ v p ∧
      (∀ (x : Space) (t : ℝ), 0 ≤ t →
        0 < clockRate x t ∧ clockRate x t ≤ 1)

/-- Adding a passive clock cannot create a missing global Euler solution. -/
theorem passiveClock_implies_euler_global (u₀ : Space → Space) :
    PassiveClockGlobal u₀ →
      ∃ (v : Space → ℝ → Space) (p : Space → ℝ → ℝ),
        Euler.EulerExistenceAndSmoothnessR3 u₀ v p := by
  rintro ⟨v, p, clockRate, hEuler, hClock⟩
  exact ⟨v, p, hEuler⟩

/-- Directly inherits the formalized Euler existence-of-breakdown theorem.
    This is a conditional impossibility statement for passive clocks only. -/
theorem passiveClock_breakdown_R3 :
    ∃ u₀ : Space → Space,
      Euler.InitialVelocityConditionDecay u₀ ∧
      ¬ PassiveClockGlobal u₀ := by
  obtain ⟨u₀, hInitial, hNoGlobal⟩ := Euler.euler_breakdown_R3
  refine ⟨u₀, hInitial, ?_⟩
  intro hClock
  exact hNoGlobal (passiveClock_implies_euler_global u₀ hClock)

/-- A separate, elementary statement: surjective reparameterization
    preserves unboundedness of a scalar observable over the whole domain.
    This is not yet the stronger limsup-at-an-endpoint theorem. -/
def UnboundedOn {Time : Type*} (f : Time → ℝ) : Prop :=
  ∀ M : ℝ, ∃ t : Time, M < f t

theorem unbounded_iff_after_surjective_time_change
    {Time Clock : Type*} (f : Time → ℝ)
    (absoluteTime : Clock → Time)
    (hSurj : Function.Surjective absoluteTime) :
    UnboundedOn f ↔ UnboundedOn (fun τ => f (absoluteTime τ)) := by
  constructor
  · intro h M
    obtain ⟨t, ht⟩ := h M
    obtain ⟨τ, hτ⟩ := hSurj t
    refine ⟨τ, ?_⟩
    simpa [hτ] using ht
  · intro h M
    obtain ⟨τ, hτ⟩ := h M
    exact ⟨absoluteTime τ, hτ⟩

end SSTFormal

#print axioms SSTFormal.passiveClock_breakdown_R3
#print axioms SSTFormal.unbounded_iff_after_surjective_time_change
