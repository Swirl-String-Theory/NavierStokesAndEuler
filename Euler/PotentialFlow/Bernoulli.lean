import Euler.PotentialFlow.Laplace
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Euler to Bernoulli reduction for potential flow

Pointwise identities are separated from the global conclusion that the
Bernoulli function is spatially constant on a connected open domain.

`C(t)` is retained as gauge freedom of the potential; it is not forced to
zero without an additional normalization hypothesis.

In addition to the pointwise/global reduction under an explicit derivative-swap
hypothesis `hswap`, this file derives `hswap` itself from joint `C²`/`C^∞`
regularity of the potential `φ` in `(t, x)`, using local mixed-partials
symmetry (`Mathlib.Analysis.Calculus.FDeriv.Symmetric`). The argument mirrors
`Euler.ComparatorBridge.spatial_fderiv_hasDerivAt` in `Euler/CurlTimeDerivative.lean`,
specialized to a scalar potential so as to avoid importing that heavier module.
-/

noncomputable section

open ContDiff InnerProductSpace Set Filter
open scoped ContDiff Topology ContDiff

namespace Euler.PotentialFlow

/-- Kinetic energy density `(1/2) * ||v||^2`. -/
def kineticEnergy (v : Space → Space) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * ‖v x‖ ^ 2

/-- Bernoulli integrand at fixed time for a scalar potential and pressure. -/
def bernoulliFunction (ρ : FluidDensity) (φ : ℝ → Space → ℝ) (p : ℝ → Space → ℝ)
    (t : ℝ) (x : Space) : ℝ :=
  deriv (fun s => φ s x) t + kineticEnergy (potentialVelocity (φ t)) x + p t x / ρ.ρ

theorem kineticEnergy_eq_half_sum_sq (v : Space → Space) (x : Space) :
    kineticEnergy v x = (1 / 2 : ℝ) * ∑ i : Fin 3, v x i ^ 2 := by
  rw [kineticEnergy, ← EuclideanSpace.real_norm_sq_eq]

theorem gradient_add {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  simp only [gradient, fderiv_fun_add hf hg, map_add]

theorem gradient_const_mul {f : Space → ℝ} {x : Space} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  simp only [gradient]
  rw [fderiv_const_mul hf c, map_smul]

theorem fderiv_eq_zero_of_gradient_eq_zero {f : Space → ℝ} {x : Space}
    (h : gradient f x = 0) : fderiv ℝ f x = 0 := by
  have := congrArg (⇑(toDual ℝ Space)) h
  simpa [toDual_gradient, map_zero] using this

theorem exists_const_of_gradient_eq_zero {f : Space → ℝ} {D : Set Space}
    (hD : IsOpen D) (hDc : IsPreconnected D)
    (hdiff : DifferentiableOn ℝ f D)
    (hgrad : ∀ x ∈ D, gradient f x = 0) :
    ∃ C : ℝ, ∀ x ∈ D, f x = C := by
  refine hD.exists_is_const_of_fderiv_eq_zero hDc hdiff ?_
  intro x hx
  exact fderiv_eq_zero_of_gradient_eq_zero (hgrad x hx)

theorem exists_bernoulli_spatial_constant
    (ρ : FluidDensity) (φ : ℝ → Space → ℝ) (p : ℝ → Space → ℝ)
    (D : Set Space) (t : ℝ)
    (hD : IsOpen D) (hDc : IsPreconnected D)
    (hdiff : DifferentiableOn ℝ (bernoulliFunction ρ φ p t) D)
    (hgrad : ∀ x ∈ D, gradient (bernoulliFunction ρ φ p t) x = 0) :
    ∃ C : ℝ, ∀ x ∈ D, bernoulliFunction ρ φ p t x = C :=
  exists_const_of_gradient_eq_zero hD hDc hdiff hgrad

private theorem fderiv_eq_sum_partial (f : Space → ℝ) (x w : Space) :
    fderiv ℝ f x w = ∑ j : Fin 3, partialDerivative f j x * w j := by
  have hinner : fderiv ℝ f x w = ⟪gradient f x, w⟫_ℝ := by
    simp [inner_gradient_left]
  rw [hinner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [gradient_coordinate, RCLike.inner_apply, mul_comm]

private theorem convectiveAccel_potential_coord (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (x : Space) (i : Fin 3) :
    convectiveAccel (potentialVelocity φ) x i =
      ∑ j : Fin 3,
        potentialVelocity φ x j * partialDerivative (partialDerivative φ i) j x := by
  have hv : DifferentiableAt ℝ (potentialVelocity φ) x :=
    ((contDiff_gradient φ hφ).differentiable (by simp)).differentiableAt
  unfold convectiveAccel
  rw [← fderiv_coordinate (potentialVelocity φ) x hv i (potentialVelocity φ x),
    fderiv_eq_sum_partial (fun y => potentialVelocity φ y i) x (potentialVelocity φ x)]
  have heq : (fun y => potentialVelocity φ y i) = partialDerivative φ i := by
    funext y; simp [potentialVelocity, gradient_coordinate]
  simp only [heq, mul_comm]

private theorem gradient_kinetic_potential_coord (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (x : Space) (i : Fin 3) :
    gradient (kineticEnergy (potentialVelocity φ)) x i =
      ∑ j : Fin 3,
        potentialVelocity φ x j * partialDerivative (partialDerivative φ j) i x := by
  have hke :
      kineticEnergy (potentialVelocity φ) =
        fun y => (1 / 2 : ℝ) * ∑ j : Fin 3, partialDerivative φ j y ^ 2 := by
    funext y
    simp [kineticEnergy_eq_half_sum_sq, potentialVelocity, gradient_coordinate]
  rw [gradient_coordinate (kineticEnergy (potentialVelocity φ)) x i, hke, partialDerivative]
  have hj (j : Fin 3) : DifferentiableAt ℝ (partialDerivative φ j) x :=
    ((contDiff_partialDerivative φ hφ j).differentiable (by simp)).differentiableAt
  have hsum :
      DifferentiableAt ℝ (fun y => ∑ j : Fin 3, partialDerivative φ j y ^ 2) x :=
    DifferentiableAt.sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hj j).pow 2
  have hfd :=
    fderiv_fun_sum (u := (Finset.univ : Finset (Fin 3))) (x := x)
      (A := fun j y => partialDerivative φ j y ^ 2)
      (fun j _ => (hj j).pow 2)
  rw [fderiv_const_mul hsum (1 / 2 : ℝ), smul_apply, hfd]
  simp only [smul_eq_mul]
  change (1 / 2 : ℝ) *
      (∑ j : Fin 3, fderiv ℝ (fun y => partialDerivative φ j y ^ 2) x)
        (EuclideanSpace.single i 1) =
    ∑ j : Fin 3, potentialVelocity φ x j * partialDerivative (partialDerivative φ j) i x
  simp only [sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpow := (HasFDerivAt.pow (n := 2) (hj j).hasFDerivAt).fderiv
  rw [hpow, smul_apply]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, potentialVelocity,
    gradient_coordinate, partialDerivative]
  ring

theorem convectiveAccel_potentialVelocity (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    convectiveAccel (potentialVelocity φ) x =
      gradient (kineticEnergy (potentialVelocity φ)) x := by
  ext i
  rw [convectiveAccel_potential_coord φ hφ x i, gradient_kinetic_potential_coord φ hφ x i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDerivative_comm φ (hφ.of_le (by simp)) i j x]

theorem gradient_bernoulli_eq_zero_of_euler
    (ρ : FluidDensity) (φ : ℝ → Space → ℝ) (p : ℝ → Space → ℝ)
    (t : ℝ) (x : Space)
    (hφt : ContDiff ℝ ∞ (φ t))
    (hswap :
      deriv (fun s => potentialVelocity (φ s) x) t =
        gradient (fun y => deriv (fun s => φ s y) t) x)
    (hmom :
      deriv (fun s => potentialVelocity (φ s) x) t +
          convectiveAccel (potentialVelocity (φ t)) x =
        -((1 / ρ.ρ) • gradient (p t) x))
    (hdt : DifferentiableAt ℝ (fun y => deriv (fun s => φ s y) t) x)
    (hp : DifferentiableAt ℝ (p t) x)
    (hke : DifferentiableAt ℝ (kineticEnergy (potentialVelocity (φ t))) x) :
    gradient (bernoulliFunction ρ φ p t) x = 0 := by
  have hconv := convectiveAccel_potentialVelocity (φ t) hφt x
  set A : Space → ℝ := fun y => deriv (fun s => φ s y) t
  set B : Space → ℝ := kineticEnergy (potentialVelocity (φ t))
  set C : Space → ℝ := fun y => (1 / ρ.ρ) * p t y
  have hpρ : DifferentiableAt ℝ C x := hp.const_mul _
  have hpress : gradient C x = (1 / ρ.ρ) • gradient (p t) x :=
    gradient_const_mul (1 / ρ.ρ) hp
  have hABC :
      bernoulliFunction ρ φ p t = fun y => A y + B y + C y := by
    funext y
    simp only [bernoulliFunction, A, B, C, div_eq_inv_mul]
    ring
  have hbridge :
      (fun y => A y + B y + C y) = fun y => (fun z => A z + B z) y + C y := by
    funext y; rfl
  have hsum :
      gradient (fun y => A y + B y + C y) x =
        gradient A x + gradient B x + gradient C x := by
    have hAB : DifferentiableAt ℝ (fun y => A y + B y) x := hdt.add hke
    have h1 := gradient_add hAB hpρ
    have h2 := gradient_add hdt hke
    rw [hbridge, h1, h2, add_assoc]
  have hB :
      gradient (bernoulliFunction ρ φ p t) x =
        gradient A x + gradient B x + (1 / ρ.ρ) • gradient (p t) x := by
    rw [hABC, hsum, hpress]
  have hmom' :
      deriv (fun s => potentialVelocity (φ s) x) t +
          gradient B x + (1 / ρ.ρ) • gradient (p t) x = 0 := by
    have h := hmom
    rw [hconv] at h
    have h' := congrArg (fun z => z + (1 / ρ.ρ) • gradient (p t) x) h
    simpa [B] using h'.trans (neg_add_cancel _)
  rw [hB, ← hswap]
  exact hmom'

theorem bernoulli_reduction
    (ρ : FluidDensity) (φ : ℝ → Space → ℝ) (p : ℝ → Space → ℝ)
    (D : Set Space) (t : ℝ)
    (hD : IsOpen D) (hDc : IsPreconnected D)
    (hφt : ContDiff ℝ ∞ (φ t))
    (hswap : ∀ x ∈ D,
      deriv (fun s => potentialVelocity (φ s) x) t =
        gradient (fun y => deriv (fun s => φ s y) t) x)
    (hmom : ∀ x ∈ D,
      deriv (fun s => potentialVelocity (φ s) x) t +
          convectiveAccel (potentialVelocity (φ t)) x =
        -((1 / ρ.ρ) • gradient (p t) x))
    (hp : DifferentiableOn ℝ (p t) D)
    (hdt : DifferentiableOn ℝ (fun y => deriv (fun s => φ s y) t) D)
    (hke : DifferentiableOn ℝ (kineticEnergy (potentialVelocity (φ t))) D)
    (hBdiff : DifferentiableOn ℝ (bernoulliFunction ρ φ p t) D) :
    ∃ C : ℝ, ∀ x ∈ D, bernoulliFunction ρ φ p t x = C := by
  apply exists_bernoulli_spatial_constant ρ φ p D t hD hDc hBdiff
  intro x hx
  exact gradient_bernoulli_eq_zero_of_euler ρ φ p t x hφt (hswap x hx) (hmom x hx)
    (hdt.differentiableAt (hD.mem_nhds hx))
    (hp.differentiableAt (hD.mem_nhds hx))
    (hke.differentiableAt (hD.mem_nhds hx))

/-! ### Deriving the derivative-swap hypothesis from joint smoothness

The hypothesis `hswap` used above says that differentiating the potential
velocity `∇φ(s, x)` in time `s` at `s = t` commutes with taking the spatial
gradient of the time derivative `∂ₛφ(s, y)|_{s=t}`. This is a standard
consequence of the symmetry of mixed second partial derivatives once `φ` is
jointly `C²` in `(t, x)`. We prove this swap locally (importing only
`Mathlib.Analysis.Calculus.FDeriv.Symmetric`) rather than reusing the vector
field version `Euler.ComparatorBridge.spatial_fderiv_hasDerivAt`, which lives
in the much heavier `Euler.CurlTimeDerivative` module. -/

/-- The ordinary spatial derivative of a time slice of a jointly differentiable
scalar function is the spatial restriction of its joint derivative. Scalar
analogue of `Euler.ComparatorBridge.fderiv_spatial_slice`. -/
private theorem fderiv_spatial_slice_scalar {u : ℝ × Space → ℝ} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u (t, x)) :
    fderiv ℝ (fun y => u (t, y)) x =
      (fderiv ℝ u (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h := hu.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  rw [show (fun y => u (t, y)) = u ∘ (fun y => (t, y)) from rfl, h.fderiv]
  congr 1

/-- The ordinary time derivative of a spatial slice of a jointly differentiable
scalar function is the time direction of its joint derivative. Scalar
analogue of `Euler.ComparatorBridge.deriv_time_slice`. -/
private theorem deriv_time_slice_scalar {u : ℝ × Space → ℝ} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u (t, x)) :
    deriv (fun r => u (r, x)) t = fderiv ℝ u (t, x) (1, 0) := by
  have h := hu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def, id_eq] using h.deriv

/-- Mixed differentiation commutes using only local joint `C²` regularity of a
scalar function: the time derivative of the spatial-derivative curve equals the
spatial derivative of the time-derivative function. Scalar analogue of
`Euler.ComparatorBridge.spatial_fderiv_hasDerivAt`. -/
private theorem spatial_fderiv_hasDerivAt_scalar {u : ℝ × Space → ℝ} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ 2 u (t, x)) :
    HasDerivAt (fun r => fderiv ℝ (fun y => u (r, y)) x)
      (fderiv ℝ (fun y => deriv (fun r => u (r, y)) t) x) t := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (t, x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt ℝ u z := by
    filter_upwards [(hu.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)]
      with z hz
    exact hz.differentiableAt (by norm_num)
  have htime := hdu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hmatrix := htime.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ Space))
  have hspatial := hdu.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hvelocity := hspatial.clm_apply (hasFDerivAt_const (1, (0 : Space)) x)
  have heq : (fun y => deriv (fun r => u (r, y)) t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u (t, y) (1, 0)) := by
    filter_upwards [((continuous_const.prodMk continuous_id).tendsto x).eventually hnear]
      with y hy
    exact deriv_time_slice_scalar hy
  have hvelocity' := hvelocity.congr_of_eventuallyEq heq
  have hderiv : fderiv ℝ (fun y => deriv (fun r => u (r, y)) t) x =
      ((fderiv ℝ (fderiv ℝ u) (t, x)) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space) := by
    rw [hvelocity'.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    simpa using hu.isSymmSndFDerivAt (by norm_num) (0, v) (1, 0)
  rw [hderiv]
  have hmatrix' : HasDerivAt (fun r => (fderiv ℝ u (r, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space))
      (((fderiv ℝ (fderiv ℝ u) (t, x)) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) t := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_zero, add_zero] using hmatrix
  apply hmatrix'.congr_of_eventuallyEq
  filter_upwards [((continuous_id.prodMk continuous_const).tendsto t).eventually hnear]
    with r hr
  exact fderiv_spatial_slice_scalar hr

/-- The derivative-swap hypothesis `hswap` follows from joint `C²` regularity of
the potential `φ` at `(t, x)`: differentiating the potential velocity in time
at `x` commutes with taking the spatial gradient of the time-derivative of
`φ`. This is the key analytic input that `gradient_bernoulli_eq_zero_of_euler`
and `bernoulli_reduction` otherwise take as a hypothesis. -/
theorem deriv_potentialVelocity_eq_gradient_deriv
    {φ : ℝ → Space → ℝ} {t : ℝ} {x : Space}
    (hφ : ContDiffAt ℝ 2 (fun q : ℝ × Space => φ q.1 q.2) (t, x)) :
    deriv (fun s => potentialVelocity (φ s) x) t =
      gradient (fun y => deriv (fun s => φ s y) t) x := by
  have key := spatial_fderiv_hasDerivAt_scalar
    (u := fun q : ℝ × Space => φ q.1 q.2) (t := t) (x := x) hφ
  have hcomp := (toDual ℝ Space).symm.hasFDerivAt.comp_hasDerivAt t key
  show deriv (fun s => (toDual ℝ Space).symm (fderiv ℝ (φ s) x)) t =
      (toDual ℝ Space).symm (fderiv ℝ (fun y => deriv (fun s => φ s y) t) x)
  exact hcomp.deriv

/-- High-level Euler-to-Bernoulli reduction assuming only joint smoothness of
the potential `φ` (rather than the derivative-swap identity `hswap` directly):
on a connected open spatial domain, the Bernoulli function is spatially
constant at each fixed time, with the constant `C(t)` left as gauge freedom. -/
theorem bernoulli_reduction_of_joint_contDiff
    (ρ : FluidDensity) (φ : ℝ → Space → ℝ) (p : ℝ → Space → ℝ)
    (D : Set Space) (t : ℝ)
    (hD : IsOpen D) (hDc : IsPreconnected D)
    (hjoint : ContDiff ℝ ∞ (fun q : ℝ × Space => φ q.1 q.2))
    (hmom : ∀ x ∈ D,
      deriv (fun s => potentialVelocity (φ s) x) t +
          convectiveAccel (potentialVelocity (φ t)) x =
        -((1 / ρ.ρ) • gradient (p t) x))
    (hp : DifferentiableOn ℝ (p t) D)
    (hdt : DifferentiableOn ℝ (fun y => deriv (fun s => φ s y) t) D)
    (hke : DifferentiableOn ℝ (kineticEnergy (potentialVelocity (φ t))) D)
    (hBdiff : DifferentiableOn ℝ (bernoulliFunction ρ φ p t) D) :
    ∃ C : ℝ, ∀ x ∈ D, bernoulliFunction ρ φ p t x = C := by
  have hφt : ContDiff ℝ ∞ (φ t) := by
    have h := hjoint.comp (contDiff_prodMk_right t)
    simpa only [Function.comp_def] using h
  have hswap : ∀ x ∈ D,
      deriv (fun s => potentialVelocity (φ s) x) t =
        gradient (fun y => deriv (fun s => φ s y) t) x := by
    intro x _
    exact deriv_potentialVelocity_eq_gradient_deriv (hjoint.contDiffAt.of_le (by norm_num))
  exact bernoulli_reduction ρ φ p D t hD hDc hφt hswap hmom hp hdt hke hBdiff

end Euler.PotentialFlow



