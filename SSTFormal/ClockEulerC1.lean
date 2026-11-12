import SSTFormal.ClockIntegral
import Euler.Solution
import Euler.ComparatorSingularityNorms
import Mathlib.Order.Filter.ENNReal

/-!
# SST-FV02-C1 — the actual Euler C¹ norm under an integrated passive clock

This is an additive, constant-blind proof attempt. The initial release proves
an endpoint-unboundedness transfer for the actual maximal Euler C¹ norm (as a
real quantity), and for its `ENNReal.ofReal` representation. The equivalence
with `Euler.velocityC1Norm` on each physical time slice is an explicit lemma.

The stronger theorem phrased as `Filter.limsup ... (𝓝[<] T) = ⊤` with the
clock-changed function is reserved for FV02-C2; do not claim that statement
is established merely because the threshold-based result compiles.

No change to Euler dynamics, no active feedback and no spatial clocks.
-/

noncomputable section

open Set
open scoped ENNReal

namespace SSTFormal

/-- A real-valued extension of the maximal Euler C¹ norm. Only 0 ≤ t < T* is
used in the proof; the value 0 outside the physical domain is conventional. -/
def eulerC1RealProfile (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ico (0 : ℝ) EulerPacketInduction.lifespan.duration then
    EulerPacketInduction.lifespan.maximalC1Norm ⟨t, ht⟩
  else 0

/-- On the maximal Euler lifespan, the profile is the actual C¹ norm. -/
theorem eulerC1RealProfile_eq (t : EulerPacketInduction.MaximalTime) :
    eulerC1RealProfile (t : ℝ) = EulerPacketInduction.maximalC1Norm t := by
  have ht : (t : ℝ) ∈ Set.Ico (0 : ℝ) EulerPacketInduction.lifespan.duration :=
    t.property
  simp [eulerC1RealProfile, ht, EulerPacketInduction.maximalC1Norm]

/-- The actual Euler maximal C¹ norm exceeds every real threshold
arbitrarily close to the finite singularity time. -/
theorem eulerC1RealProfile_unboundedNearLeft :
    UnboundedNearLeft eulerC1RealProfile EulerPacketInduction.lifespan.duration := by
  intro M a ha
  obtain ⟨t, hat, hM⟩ :=
    EulerPacketInduction.lifespan.maximalC1Norm_unbounded_near_endpoint a M ha
  refine ⟨(t : ℝ), hat, t.property.2, ?_⟩
  rw [eulerC1RealProfile_eq t]
  exact hM

/-- FV02-B discharges all endpoint correspondence requirements for this
specific Euler C¹ norm, with a strictly positive continuous clock rate. -/
theorem eulerC1_unbounded_after_integrated_clock
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t) :
    UnboundedNearLeft
      (fun τ => eulerC1RealProfile
        (inverseClock q hq hqpos EulerPacketInduction.lifespan.duration
          EulerPacketInduction.lifespan.duration_pos τ))
      (clockPrimitive q EulerPacketInduction.lifespan.duration) := by
  exact (unboundedNearLeft_iff_after_integrated_clock q hq hqpos
    EulerPacketInduction.lifespan.duration
    EulerPacketInduction.lifespan.duration_pos eulerC1RealProfile).mp
      eulerC1RealProfile_unboundedNearLeft

/-- Arbitrarily high finite ENNReal thresholds near a left endpoint. -/
def ENNUnboundedNearLeft (f : ℝ → ENNReal) (T : ℝ) : Prop :=
  ∀ M : ENNReal, M < ⊤ → ∀ a : ℝ, a < T →
    ∃ t : ℝ, a < t ∧ t < T ∧ M < f t

/-- Transfer a real-valued threshold theorem to an extended-nonnegative
threshold theorem. This does not yet rewrite a Filter.limsup expression. -/
theorem ennUnboundedNearLeft_of_real
    (f : ℝ → ℝ) (T : ℝ) (hf : UnboundedNearLeft f T) :
    ENNUnboundedNearLeft (fun t => ENNReal.ofReal (f t)) T := by
  intro M hM a ha
  obtain ⟨t, hat, htT, hMt⟩ := hf M.toReal a ha
  exact ⟨t, hat, htT,
    (ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt hM)).mpr hMt⟩

/-- Actual Euler C¹ blow-up survives the integrated passive clock even
when the norm is regarded as an extended nonnegative real. -/
theorem eulerC1ENN_unbounded_after_integrated_clock
    (q : ℝ → ℝ) (hq : Continuous q) (hqpos : ∀ t : ℝ, 0 < q t) :
    ENNUnboundedNearLeft
      (fun τ => ENNReal.ofReal (eulerC1RealProfile
        (inverseClock q hq hqpos EulerPacketInduction.lifespan.duration
          EulerPacketInduction.lifespan.duration_pos τ)))
      (clockPrimitive q EulerPacketInduction.lifespan.duration) := by
  exact ennUnboundedNearLeft_of_real _ _
    (eulerC1_unbounded_after_integrated_clock q hq hqpos)

/-- Identification with the comparator's actual extended Euler C¹ norm
on each physical time slice; follows from the existing comparator norm
identity, not from a new hydrodynamic assumption. -/
theorem eulerC1_ofReal_eq_comparator (t : EulerPacketInduction.MaximalTime) :
    ENNReal.ofReal (EulerPacketInduction.maximalC1Norm t) =
      Euler.velocityC1Norm (EulerPacketInduction.maximalVelocity t) := by
  simpa [EulerPacketInduction.maximalC1Norm,
    EulerPacketInduction.maximalVelocity,
    EulerOrdinarySobolev.FiniteLifespan.maximalC1Norm,
    EulerOrdinarySobolev.FiniteLifespan.maximalVelocityNorm,
    EulerOrdinarySobolev.FiniteLifespan.maximalGradientNorm,
    EulerOrdinarySobolev.FiniteLifespan.maximalVelocity] using
    (Euler.ComparatorBridge.velocityC1Norm_eq
      (EulerPacketInduction.lifespan.maximalField t)).symm

end SSTFormal

#print axioms SSTFormal.eulerC1RealProfile_eq
#print axioms SSTFormal.eulerC1RealProfile_unboundedNearLeft
#print axioms SSTFormal.eulerC1_unbounded_after_integrated_clock
#print axioms SSTFormal.ennUnboundedNearLeft_of_real
#print axioms SSTFormal.eulerC1ENN_unbounded_after_integrated_clock
#print axioms SSTFormal.eulerC1_ofReal_eq_comparator
