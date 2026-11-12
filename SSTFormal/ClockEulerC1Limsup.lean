import SSTFormal.ClockEulerC1
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Order.Filter.ENNReal

/-!
# SST-FV02-C2 — ENNReal endpoint limsup for an integrated passive clock

This ADDITIVE module upgrades the endpoint-threshold facts of FV02-C1 to
literal `Filter.limsup ... (𝓝[<] endpoint) = ⊤` statements.

Important: no change to Euler's equations, no spatial clock foliation,
and no active Swirl Clock feedback. The global scalar clock rate `q`
is assumed continuous and strictly positive on all of ℝ, as in FV02-B.
This is stronger than an almost-everywhere-positive `L¹` rate.

A theorem on a scalar time observable is not by itself a theorem about
arbitrary space-dependent clocks; the `eulerC1RealProfile` identification
with the actual Euler C¹ norm comes from FV02-C1.
-/

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SSTFormal

/-- Threshold-unboundedness on every terminal left interval implies an
actual infinite extended-real filter-limsup. This is stated for a general
`ℝ → ENNReal` observable and does not assume time continuity. -/
theorem enn_limsup_eq_top_of_unboundedNearLeft
    (f : ℝ → ENNReal) (T : ℝ)
    (hf : ENNUnboundedNearLeft f T) :
    Filter.limsup f (𝓝[<] T) = (⊤ : ENNReal) := by
  let : Nonempty (Set.Iio T) := ⟨⟨T - 1, by simp⟩⟩
  have hsub :
      Filter.limsup (fun t : Set.Iio T => f (t : ℝ))
        (atTop : Filter (Set.Iio T)) = (⊤ : ENNReal) := by
    apply top_unique
    apply (Filter.le_limsup_iff).2
    intro b hb
    apply frequently_atTop.mpr
    intro s
    obtain ⟨t, hst, htT, hbt⟩ := hf b hb (s : ℝ) s.property
    exact ⟨⟨t, htT⟩, le_of_lt hst, hbt⟩
  have hmap :
      Filter.map (fun t : Set.Iio T => (t : ℝ))
          (atTop : Filter (Set.Iio T)) = (𝓝[<] T) :=
    map_coe_Iio_atTop T
  -- `limsup (f ∘ ↑) atTop = limsup f (map ↑ atTop)` by definition of `Filter.limsup`.
  rw [← hmap, ← Filter.limsup_comp]
  exact hsub

/-- Before changing clocks, the actual maximal Euler C¹ norm has infinite
`ENNReal` left-endpoint limsup, using the bounded-field norm profile. -/
theorem eulerC1ENN_limsup_before_integrated_clock :
    Filter.limsup (fun t : ℝ => ENNReal.ofReal (eulerC1RealProfile t))
      (𝓝[<] EulerPacketInduction.lifespan.duration) = ⊤ := by
  exact enn_limsup_eq_top_of_unboundedNearLeft _ _
    (ennUnboundedNearLeft_of_real _ _ eulerC1RealProfile_unboundedNearLeft)

/-- Core FV02-C2 claim. For any continuous positive scalar clock rate, the
actual maximal Euler C¹ norm has infinite extended-nonnegative limsup
approaching the *operational* clock endpoint from the left. -/
theorem eulerC1ENN_limsup_after_integrated_clock
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t) :
    Filter.limsup
      (fun τ : ℝ => ENNReal.ofReal (eulerC1RealProfile
        (inverseClock q hq hqpos EulerPacketInduction.lifespan.duration
          EulerPacketInduction.lifespan.duration_pos τ)))
      (𝓝[<] (clockPrimitive q EulerPacketInduction.lifespan.duration)) = ⊤ := by
  exact enn_limsup_eq_top_of_unboundedNearLeft _ _
    (eulerC1ENN_unbounded_after_integrated_clock q hq hqpos)

end SSTFormal

#print axioms SSTFormal.enn_limsup_eq_top_of_unboundedNearLeft
#print axioms SSTFormal.eulerC1ENN_limsup_before_integrated_clock
#print axioms SSTFormal.eulerC1ENN_limsup_after_integrated_clock
