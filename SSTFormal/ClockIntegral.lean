import SSTFormal.ClockEndpoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# SST-FV02 Stage B — Clock integral and endpoint inverse

Constant-blind formalization. We assume a continuous and everywhere
strictly positive dimensionless clock rate `q : ℝ → ℝ`. These hypotheses
are *stronger* than positivity almost everywhere on the physical interval.

The active Euler dynamics are untouched. This module:
  1. defines the primitive tau(t) = integral_0^t q(s) ds;
  2. proves its derivative, continuity, and strict monotonicity;
  3. obtains an inverse for every clock time in (0, tau(T));
  4. derives the previously *assumed* EndpointClockCorrespondence; and
  5. composes Stage B with the Stage A endpoint-unboundedness theorem.

The inverse is chosen noncomputably on the physical interval and is assigned
zero outside. No global surjectivity of the primitive is assumed or claimed.
No claim is made about an active Swirl Clock coupling or spatially varying
clock fields.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace SSTFormal

/-- Operational time accumulated from a continuous clock rate. -/
def clockPrimitive (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, q s

@[simp] theorem clockPrimitive_zero (q : ℝ → ℝ) : clockPrimitive q 0 = 0 := by
  simp [clockPrimitive]

/-- The fundamental theorem of calculus identifies the clock rate. -/
theorem clockPrimitive_hasDerivAt (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) :
    HasDerivAt (clockPrimitive q) (q t) t := by
  -- Unfold first so Lean elaborates `HasDerivAt` with the same instances as the FTC lemma.
  unfold clockPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (hq.intervalIntegrable 0 t)
    (hq.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t))
    hq.continuousAt

/-- Continuous integral primitive on the entire absolute-time line. -/
theorem clockPrimitive_continuous (q : ℝ → ℝ) (hq : Continuous q) :
    Continuous (clockPrimitive q) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (clockPrimitive_hasDerivAt q hq t).continuousAt

/-- Strict positivity of clock rate implies strict monotonicity of tau(t). -/
theorem clockPrimitive_strictMono (q : ℝ → ℝ) (hq : Continuous q)
    (hqpos : ∀ t : ℝ, 0 < q t) : StrictMono (clockPrimitive q) := by
  apply strictMono_of_deriv_pos
  intro t
  have hderiv : deriv (clockPrimitive q) t = q t :=
    (clockPrimitive_hasDerivAt q hq t).deriv
  rw [hderiv]
  exact hqpos t

/-- A positive absolute-time duration has a positive clock-time duration. -/
theorem clockEndpoint_pos (q : ℝ → ℝ) (hq : Continuous q)
    (hqpos : ∀ t : ℝ, 0 < q t) {T : ℝ} (hT : 0 < T) :
    0 < clockPrimitive q T := by
  have hmono := clockPrimitive_strictMono q hq hqpos
  simpa using hmono hT

/-- Every internal operational time comes from a unique absolute time in (0,T).
    Existence is stated separately from uniqueness to make its dependence on
    the intermediate-value theorem auditable. -/
theorem clockPrimitive_exists_preimage
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t)
    (T : ℝ) (_hT : 0 < T) (τ : ℝ)
    (hτ0 : 0 < τ) (hτT : τ < clockPrimitive q T) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ clockPrimitive q t = τ := by
  have himage := (clockPrimitive_continuous q hq).image_Ioo_of_strictMono
    (clockPrimitive_strictMono q hq hqpos) (a := (0 : ℝ)) (b := T)
  have hmem : τ ∈ Set.Ioo (clockPrimitive q 0) (clockPrimitive q T) := by
    simpa using (show (0 : ℝ) < τ ∧ τ < clockPrimitive q T from ⟨hτ0, hτT⟩)
  rw [← himage] at hmem
  rcases hmem with ⟨t, ht, hval⟩
  exact ⟨t, ht.1, ht.2, hval⟩

/-- A total extension of the inverse clock; only the physical interval
    0 < τ < tau(T) is used in any theorem. -/
noncomputable def inverseClock
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t)
    (T : ℝ) (hT : 0 < T) (τ : ℝ) : ℝ :=
  if hτ : 0 < τ ∧ τ < clockPrimitive q T then
    Classical.choose (clockPrimitive_exists_preimage q hq hqpos T hT τ hτ.1 hτ.2)
  else 0

/-- An internal clock time has an inverse in (0,T) with exact clock value. -/
theorem inverseClock_spec
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t)
    (T : ℝ) (hT : 0 < T) (τ : ℝ)
    (hτ : 0 < τ ∧ τ < clockPrimitive q T) :
    0 < inverseClock q hq hqpos T hT τ ∧
    inverseClock q hq hqpos T hT τ < T ∧
    clockPrimitive q (inverseClock q hq hqpos T hT τ) = τ := by
  unfold inverseClock
  simp only [hτ]
  exact Classical.choose_spec
    (clockPrimitive_exists_preimage q hq hqpos T hT τ hτ.1 hτ.2)

/-- The inverse recovers every absolute time in the physical interval. -/
theorem inverseClock_clockPrimitive
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t)
    (T : ℝ) (hT : 0 < T) (t : ℝ) (ht : 0 < t ∧ t < T) :
    inverseClock q hq hqpos T hT (clockPrimitive q t) = t := by
  have hmono := clockPrimitive_strictMono q hq hqpos
  have hτ : 0 < clockPrimitive q t ∧ clockPrimitive q t < clockPrimitive q T := by
    constructor
    · simpa using hmono ht.1
    · exact hmono ht.2
  have hspec := inverseClock_spec q hq hqpos T hT (clockPrimitive q t) hτ
  exact hmono.injective hspec.2.2

/-- The inverse integrated clock satisfies BOTH endpoint-neighborhood
    requirements of SST-FV02 Stage A, rather than assuming them. -/
theorem inverseClock_endpointCorrespondence
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t)
    (T : ℝ) (hT : 0 < T) :
    EndpointClockCorrespondence (inverseClock q hq hqpos T hT)
      T (clockPrimitive q T) := by
  let τstar := clockPrimitive q T
  let inv := inverseClock q hq hqpos T hT
  have hmono : StrictMono (clockPrimitive q) :=
    clockPrimitive_strictMono q hq hqpos
  have hτpos : 0 < τstar := clockEndpoint_pos q hq hqpos hT
  constructor
  · intro a ha
    have hmax : max a 0 < τstar := (max_lt_iff).2 ⟨ha, hτpos⟩
    let τmid : ℝ := (max a 0 + τstar) / 2
    have hτmid0 : 0 < τmid := by
      dsimp [τmid]
      have hz : (0 : ℝ) ≤ max a 0 := le_max_right a 0
      linarith
    have hτmidT : τmid < τstar := by
      dsimp [τmid]
      linarith
    have haτmid : a < τmid := by
      dsimp [τmid]
      have hz : a ≤ max a 0 := le_max_left a 0
      linarith
    obtain ⟨b, hb0, hbT, hbval⟩ :=
      clockPrimitive_exists_preimage q hq hqpos T hT τmid hτmid0 hτmidT
    refine ⟨b, hbT, ?_⟩
    intro t hbt htT
    let τ : ℝ := clockPrimitive q t
    have ht0 : 0 < t := lt_trans hb0 hbt
    have hτ0 : 0 < τ := by
      dsimp [τ]
      simpa using hmono ht0
    have hτT : τ < τstar := hmono htT
    have haτ : a < τ := by
      have hsmall := hmono hbt
      rw [hbval] at hsmall
      exact lt_trans haτmid hsmall
    have hinv : inv τ = t := by
      change inverseClock q hq hqpos T hT (clockPrimitive q t) = t
      exact inverseClock_clockPrimitive q hq hqpos T hT t ⟨ht0, htT⟩
    exact ⟨τ, haτ, hτT, hinv⟩
  · intro b hbT
    have hmax : max b 0 < T := (max_lt_iff).2 ⟨hbT, hT⟩
    let tmid : ℝ := (max b 0 + T) / 2
    have htmid0 : 0 < tmid := by
      dsimp [tmid]
      have hz : (0 : ℝ) ≤ max b 0 := le_max_right b 0
      linarith
    have htmidT : tmid < T := by
      dsimp [tmid]
      linarith
    have hbtmid : b < tmid := by
      dsimp [tmid]
      have hz : b ≤ max b 0 := le_max_left b 0
      linarith
    let a : ℝ := clockPrimitive q tmid
    have haT : a < τstar := hmono htmidT
    refine ⟨a, haT, ?_⟩
    intro τ haτ hτT
    have ha0 : 0 < a := by
      dsimp [a]
      simpa using hmono htmid0
    have hτ0 : 0 < τ := lt_trans ha0 haτ
    have hspec := inverseClock_spec q hq hqpos T hT τ ⟨hτ0, hτT⟩
    have htmid_inv : tmid < inv τ := by
      by_contra hn
      have hle : inv τ ≤ tmid := le_of_not_gt hn
      have hclock_le : clockPrimitive q (inv τ) ≤ clockPrimitive q tmid :=
        hmono.monotone hle
      have hclock_eq : clockPrimitive q (inv τ) = τ := hspec.2.2
      rw [hclock_eq] at hclock_le
      exact (not_le_of_gt haτ) hclock_le
    exact ⟨lt_trans hbtmid htmid_inv, hspec.2.1⟩

/-- Stage B discharges the Stage A correspondence hypothesis for a clock
    generated by integrating a continuous, strictly positive rate. -/
theorem unboundedNearLeft_iff_after_integrated_clock
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t)
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) :
    UnboundedNearLeft f T ↔
      UnboundedNearLeft
        (fun τ => f (inverseClock q hq hqpos T hT τ))
        (clockPrimitive q T) := by
  exact unboundedNearLeft_iff_after_endpoint_clock
    f (inverseClock q hq hqpos T hT) T (clockPrimitive q T)
      (inverseClock_endpointCorrespondence q hq hqpos T hT)

end SSTFormal

#print axioms SSTFormal.clockPrimitive_hasDerivAt
#print axioms SSTFormal.clockPrimitive_strictMono
#print axioms SSTFormal.clockPrimitive_exists_preimage
#print axioms SSTFormal.inverseClock_spec
#print axioms SSTFormal.inverseClock_endpointCorrespondence
#print axioms SSTFormal.unboundedNearLeft_iff_after_integrated_clock
