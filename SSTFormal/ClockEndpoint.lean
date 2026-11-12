import Euler.Solution

/-!
# SST-FV02 (stage A): Endpoint blow-up under a passive time change

This is an ADDITIVE mathematical module. It does not change the unforced
Euler dynamics and uses no SST/quantum calibration constants.

A real observable is endpoint-unbounded if it exceeds every threshold
arbitrarily close to a finite endpoint from the left.

An EndpointClockCorrespondence explicitly expresses the two near-endpoint
properties of a valid inverse clock change. It does NOT follow from the
mere positivity of an unspecified scalar clock rate: a separate theorem
must establish it from clock regularity and integration.

This module proves equivalence under these precisely stated assumptions.
It is not yet a fully formalized theorem about the Euler C^1 (ENNReal)
limsup in Euler.Solution, nor about active feedback.
-/

namespace SSTFormal

/-- An observable exceeds every bound arbitrarily close to the endpoint,
    approached from the left. This is a real-valued endpoint notion. -/
def UnboundedNearLeft (f : ℝ → ℝ) (endpoint : ℝ) : Prop :=
  ∀ (M a : ℝ), a < endpoint →
    ∃ t : ℝ, a < t ∧ t < endpoint ∧ M < f t

/-- The two local properties required to translate endpoint behavior.

  * `absoluteToClock`: every sufficiently late absolute time has a clock
    preimage in any selected late clock interval.
  * `clockToAbsolute`: every sufficiently late clock time maps into any
    selected late absolute interval.

These conditions deliberately state the endpoint-coverage assumptions rather
than silently inferring them from an arbitrary function named a clock. -/
def EndpointClockCorrespondence
    (absoluteTime : ℝ → ℝ) (Tstar taustar : ℝ) : Prop :=
  (∀ a : ℝ, a < taustar →
    ∃ b : ℝ, b < Tstar ∧
      ∀ t : ℝ, b < t → t < Tstar →
        ∃ τ : ℝ, a < τ ∧ τ < taustar ∧ absoluteTime τ = t) ∧
  (∀ b : ℝ, b < Tstar →
    ∃ a : ℝ, a < taustar ∧
      ∀ τ : ℝ, a < τ → τ < taustar →
        b < absoluteTime τ ∧ absoluteTime τ < Tstar)

/-- Endpoint-unboundedness is invariant under a time change that genuinely
    identifies left neighborhoods of the two endpoints. -/
theorem unboundedNearLeft_iff_after_endpoint_clock
    (f absoluteTime : ℝ → ℝ) (Tstar taustar : ℝ)
    (hclock : EndpointClockCorrespondence absoluteTime Tstar taustar) :
    UnboundedNearLeft f Tstar ↔
      UnboundedNearLeft (fun τ => f (absoluteTime τ)) taustar := by
  constructor
  · intro h M a ha
    obtain ⟨b, hb, hLift⟩ := hclock.1 a ha
    obtain ⟨t, hbt, htT, hMt⟩ := h M b hb
    obtain ⟨τ, haτ, hτT, hτt⟩ := hLift t hbt htT
    refine ⟨τ, haτ, hτT, ?_⟩
    simpa [hτt] using hMt
  · intro h M b hb
    obtain ⟨a, ha, hMap⟩ := hclock.2 b hb
    obtain ⟨τ, haτ, hτT, hMτ⟩ := h M a ha
    obtain ⟨hbt, htT⟩ := hMap τ haτ hτT
    exact ⟨absoluteTime τ, hbt, htT, hMτ⟩

/-- A one-way form making the 'passive clocks do not cure endpoint blow-up'
    implication directly usable in later SST modules. -/
theorem endpoint_blowup_survives_passive_clock
    (f absoluteTime : ℝ → ℝ) (Tstar taustar : ℝ)
    (hclock : EndpointClockCorrespondence absoluteTime Tstar taustar)
    (hblowup : UnboundedNearLeft f Tstar) :
    UnboundedNearLeft (fun τ => f (absoluteTime τ)) taustar :=
  (unboundedNearLeft_iff_after_endpoint_clock
    f absoluteTime Tstar taustar hclock).mp hblowup

end SSTFormal

#print axioms SSTFormal.unboundedNearLeft_iff_after_endpoint_clock
#print axioms SSTFormal.endpoint_blowup_survives_passive_clock
