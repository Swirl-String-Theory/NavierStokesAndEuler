import Euler.PotentialFlow.ExteriorDomain

/-!
# Local irrotationality versus global circulation

Local irrotationality does not imply vanishing circulation, nor a single-valued
global scalar potential. This module records a checkable 2D witness and marks
general 3D knotted exteriors as blocked.

## v0.1.1 upgrades

* `vortexVelocity2D` is proved jointly smooth (`ContDiffOn ℝ ∞`) on `puncturedPlane`,
  rather than merely assumed smooth.
* The curl-free identity for `vortexVelocity2D` is proved directly by algebraic
  differentiation of the quotient components, rather than assumed via
  `PlanarVortexIrrotationalHypothesis`.
* `local_irrotational_with_nonzero_circulation` is now an unconditional theorem
  (no hypothesis argument): smoothness and curl-freeness are both proved facts.
* `HasGlobalScalarPotential2D` is introduced (Plane-local analogue of
  `HasGlobalScalarPotential`) and `vortexVelocity2D` is proved to have *no* such
  global potential on `puncturedPlane`, via the fundamental theorem of calculus
  applied along `unitCircle` against the nonzero circulation `2π`.
-/

noncomputable section

open Classical ContDiff Set Real MeasureTheory InnerProductSpace
open scoped Real Topology ContDiff

namespace Euler.PotentialFlow

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def puncturedPlane : Set Plane := {x : Plane | x ≠ 0}

theorem isOpen_puncturedPlane : IsOpen puncturedPlane := isOpen_ne

def vortexVelocity2D (x : Plane) : Plane :=
  let r2 := x 0 ^ 2 + x 1 ^ 2
  WithLp.toLp 2 ![(-x 1) / r2, x 0 / r2]

theorem r2_ne_zero_of_mem_puncturedPlane {x : Plane} (hx : x ∈ puncturedPlane) :
    x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
  have hx' : x ≠ 0 := hx
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  have hnormsq : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hnormsq
  exact hnormsq

private theorem contDiff_coord (i : Fin 2) : ContDiff ℝ ∞ (fun x : Plane => x i) :=
  contDiff_piLp_apply (𝕜 := ℝ) 2 (n := ∞)

private theorem contDiff_r2 : ContDiff ℝ ∞ (fun x : Plane => x 0 ^ 2 + x 1 ^ 2) :=
  ((contDiff_coord 0).pow 2).add ((contDiff_coord 1).pow 2)

theorem vortexVelocity2D_apply_zero (x : Plane) :
    vortexVelocity2D x 0 = (-x 1) / (x 0 ^ 2 + x 1 ^ 2) := by
  simp [vortexVelocity2D]

theorem vortexVelocity2D_apply_one (x : Plane) :
    vortexVelocity2D x 1 = x 0 / (x 0 ^ 2 + x 1 ^ 2) := by
  simp [vortexVelocity2D]

theorem contDiffOn_vortexVelocity2D_apply_zero :
    ContDiffOn ℝ ∞ (fun x : Plane => vortexVelocity2D x 0) puncturedPlane := by
  have heq : (fun x : Plane => vortexVelocity2D x 0) =
      fun x => (-x 1) / (x 0 ^ 2 + x 1 ^ 2) := funext vortexVelocity2D_apply_zero
  rw [heq]
  exact ((contDiff_coord 1).neg.contDiffOn).div contDiff_r2.contDiffOn
    (fun x hx => r2_ne_zero_of_mem_puncturedPlane hx)

theorem contDiffOn_vortexVelocity2D_apply_one :
    ContDiffOn ℝ ∞ (fun x : Plane => vortexVelocity2D x 1) puncturedPlane := by
  have heq : (fun x : Plane => vortexVelocity2D x 1) =
      fun x => x 0 / (x 0 ^ 2 + x 1 ^ 2) := funext vortexVelocity2D_apply_one
  rw [heq]
  exact (contDiff_coord 0).contDiffOn.div contDiff_r2.contDiffOn
    (fun x hx => r2_ne_zero_of_mem_puncturedPlane hx)

/-- `vortexVelocity2D` is jointly smooth on the punctured plane: each coordinate is a
quotient of smooth functions with nonvanishing denominator `x 0 ^ 2 + x 1 ^ 2`. -/
theorem contDiffOn_vortexVelocity2D : ContDiffOn ℝ ∞ vortexVelocity2D puncturedPlane := by
  apply contDiffOn_piLp'
  intro i
  fin_cases i
  · exact contDiffOn_vortexVelocity2D_apply_zero
  · exact contDiffOn_vortexVelocity2D_apply_one

def unitCircle (θ : ℝ) : Plane := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

def unitCircleDeriv (θ : ℝ) : Plane := WithLp.toLp 2 ![(-Real.sin θ), Real.cos θ]

theorem unitCircle_ne_zero (θ : ℝ) : unitCircle θ ≠ 0 := by
  intro h
  have hc : Real.cos θ = 0 := by
    simpa [unitCircle] using congrArg (fun z : Plane => (z 0 : ℝ)) h
  have hs : Real.sin θ = 0 := by
    simpa [unitCircle] using congrArg (fun z : Plane => (z 1 : ℝ)) h
  have := Real.cos_sq_add_sin_sq θ
  simp [hc, hs] at this

def circulationIntegrand (θ : ℝ) : ℝ :=
  let v := vortexVelocity2D (unitCircle θ)
  let w := unitCircleDeriv θ
  v 0 * w 0 + v 1 * w 1

theorem circulationIntegrand_eq_one (θ : ℝ) : circulationIntegrand θ = 1 := by
  have hr : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  simp [circulationIntegrand, vortexVelocity2D, unitCircle, unitCircleDeriv, hr]
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem integral_one_Icc_zero_two_pi :
    ∫ _θ in Icc (0 : ℝ) (2 * Real.pi), (1 : ℝ) = 2 * Real.pi := by
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  simp [integral_const, Measure.real, Real.volume_Icc, hπ, sub_zero, smul_eq_mul]

theorem vortex_circulation_unitCircle :
    ∫ θ in Icc (0 : ℝ) (2 * Real.pi), circulationIntegrand θ = 2 * Real.pi := by
  have h1 : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), circulationIntegrand θ = 1 := fun _ _ =>
    circulationIntegrand_eq_one _
  rw [setIntegral_congr_fun measurableSet_Icc h1]
  exact integral_one_Icc_zero_two_pi

theorem vortex_circulation_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by
  positivity

/-! ## Curl-free identity (proved, not assumed)

The curl-free identity is established pointwise by computing both mixed partial
derivatives as explicit single-variable derivatives along the coordinate axes
(via Mathlib's line-derivative API), then simplifying algebraically. -/

private theorem hasDerivAt_along_single (f : Plane → ℝ) (x : Plane) (i : Fin 2)
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single i (1 : ℝ)))
      (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) 0 :=
  hf.hasFDerivAt.hasLineDerivAt (EuclideanSpace.single i (1 : ℝ))

private theorem coord_shift_same (x : Plane) (t : ℝ) (i : Fin 2) :
    (x + t • EuclideanSpace.single i (1 : ℝ)) i = x i + t := by
  simp

private theorem coord_shift_other (x : Plane) (t : ℝ) (i j : Fin 2) (hij : j ≠ i) :
    (x + t • EuclideanSpace.single i (1 : ℝ)) j = x j := by
  simp [hij]

/-- The curl-free identity for `vortexVelocity2D`, proved unconditionally by
algebraic differentiation of the quotient components. -/
theorem curl_free_vortexVelocity2D :
    ∀ x ∈ puncturedPlane,
      fderiv ℝ (fun y => vortexVelocity2D y 1) x (EuclideanSpace.single 0 1) -
        fderiv ℝ (fun y => vortexVelocity2D y 0) x (EuclideanSpace.single 1 1) = 0 := by
  intro x hx
  have hr2 : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := r2_ne_zero_of_mem_puncturedPlane hx
  have hd1 : DifferentiableAt ℝ (fun y : Plane => vortexVelocity2D y 1) x :=
    (contDiffOn_vortexVelocity2D_apply_one.differentiableOn (by simp)).differentiableAt
      (isOpen_puncturedPlane.mem_nhds hx)
  have hd0 : DifferentiableAt ℝ (fun y : Plane => vortexVelocity2D y 0) x :=
    (contDiffOn_vortexVelocity2D_apply_zero.differentiableOn (by simp)).differentiableAt
      (isOpen_puncturedPlane.mem_nhds hx)
  -- directional derivative of `v 1` along `e0`
  have hD1 := hasDerivAt_along_single (fun y => vortexVelocity2D y 1) x 0 hd1
  have heq1 : (fun t : ℝ => vortexVelocity2D (x + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 1) =
      fun t : ℝ => (x 0 + t) / ((x 0 + t) ^ 2 + x 1 ^ 2) := by
    funext t
    rw [vortexVelocity2D_apply_one, coord_shift_same x t 0,
      coord_shift_other x t 0 1 (by decide)]
  rw [heq1] at hD1
  have hc0 := (hasDerivAt_id (0 : ℝ)).const_add (x 0)
  have hden0 := (hc0.pow 2).add_const (x 1 ^ 2)
  have hq1 := hc0.fun_div hden0 (show (x 0 + (0 : ℝ)) ^ 2 + x 1 ^ 2 ≠ 0 by simpa using hr2)
  have hval1 := hD1.unique hq1
  -- directional derivative of `v 0` along `e1`
  have hD0 := hasDerivAt_along_single (fun y => vortexVelocity2D y 0) x 1 hd0
  have heq0 : (fun t : ℝ => vortexVelocity2D (x + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0) =
      fun t : ℝ => (-(x 1 + t)) / (x 0 ^ 2 + (x 1 + t) ^ 2) := by
    funext t
    rw [vortexVelocity2D_apply_zero, coord_shift_same x t 1,
      coord_shift_other x t 1 0 (by decide)]
  rw [heq0] at hD0
  have hc1 := ((hasDerivAt_id (0 : ℝ)).const_add (x 1)).fun_neg
  have hden1 := (((hasDerivAt_id (0 : ℝ)).const_add (x 1)).pow 2).const_add (x 0 ^ 2)
  have hq0 := hc1.fun_div hden1 (show x 0 ^ 2 + (x 1 + (0 : ℝ)) ^ 2 ≠ 0 by simpa using hr2)
  have hval0 := hD0.unique hq0
  simp only [id_eq, add_zero, Pi.pow_apply] at hval1 hval0
  rw [hval1, hval0]
  ring

structure PlanarVortexIrrotationalHypothesis : Prop where
  smooth_on_punctured : ContDiffOn ℝ ∞ vortexVelocity2D puncturedPlane
  curl_free :
    ∀ x ∈ puncturedPlane,
      fderiv ℝ (fun y => vortexVelocity2D y 1) x (EuclideanSpace.single 0 1) -
        fderiv ℝ (fun y => vortexVelocity2D y 0) x (EuclideanSpace.single 1 1) = 0

/-- Both fields of `PlanarVortexIrrotationalHypothesis` are proved facts, not
assumptions: smoothness and curl-freeness of `vortexVelocity2D` on `puncturedPlane`
are established directly above. -/
theorem vortexVelocity2D_isPlanarVortexIrrotational : PlanarVortexIrrotationalHypothesis :=
  ⟨contDiffOn_vortexVelocity2D, curl_free_vortexVelocity2D⟩

/-- Local irrotationality coexists with a nonzero circulation integral. Unlike the
v0.1.0 version, this is now unconditional: no hypothesis is assumed, since both the
curl-free identity and the circulation computation are proved facts. -/
theorem local_irrotational_with_nonzero_circulation :
    (∀ x ∈ puncturedPlane,
        fderiv ℝ (fun y => vortexVelocity2D y 1) x (EuclideanSpace.single 0 1) -
          fderiv ℝ (fun y => vortexVelocity2D y 0) x (EuclideanSpace.single 1 1) = 0) ∧
      (∫ θ in Icc (0 : ℝ) (2 * Real.pi), circulationIntegrand θ = 2 * Real.pi) ∧
      ((2 * Real.pi : ℝ) ≠ 0) :=
  ⟨vortexVelocity2D_isPlanarVortexIrrotational.curl_free, vortex_circulation_unitCircle,
    vortex_circulation_ne_zero⟩

/-! ## No global scalar potential on the punctured plane

We introduce a 2D, `Plane`-local analogue of `HasGlobalScalarPotential` (which lives
in `Definitions.lean` for the 3D `Space`), and prove that `vortexVelocity2D` admits no
such global potential on `puncturedPlane`. -/

/-- Global single-valued scalar potential representation on a 2D domain `D ⊆ Plane`. -/
def HasGlobalScalarPotential2D (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ φ : Plane → ℝ, ContDiffOn ℝ ∞ φ D ∧ ∀ x ∈ D, v x = gradient φ x

private theorem hasFDerivAt_cosSinVec (θ : ℝ) :
    HasFDerivAt (fun x : ℝ => (![Real.cos x, Real.sin x] : Fin 2 → ℝ))
      (ContinuousLinearMap.toSpanSingleton ℝ (![(-Real.sin θ), Real.cos θ] : Fin 2 → ℝ)) θ := by
  apply hasFDerivAt_pi'.2
  intro i
  have hcomp :
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (![(-Real.sin θ), Real.cos θ] : Fin 2 → ℝ)) =
        ContinuousLinearMap.toSpanSingleton ℝ (![(-Real.sin θ), Real.cos θ] i) := by
    apply ContinuousLinearMap.ext
    intro t
    fin_cases i <;> simp
  rw [hcomp]
  fin_cases i
  · simpa using (Real.hasDerivAt_cos θ).hasFDerivAt
  · simpa using (Real.hasDerivAt_sin θ).hasFDerivAt

/-- The unit-circle parametrization is differentiable, with the expected tangent
vector `unitCircleDeriv θ`. -/
private theorem hasDerivAt_unitCircle (θ : ℝ) : HasDerivAt unitCircle (unitCircleDeriv θ) θ := by
  have hvecD : HasDerivAt (fun x : ℝ => (![Real.cos x, Real.sin x] : Fin 2 → ℝ))
      (![(-Real.sin θ), Real.cos θ] : Fin 2 → ℝ) θ := by
    simpa using (hasFDerivAt_cosSinVec θ).hasDerivAt
  have htoLp : HasFDerivAt (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
      (![Real.cos θ, Real.sin θ]) :=
    PiLp.hasFDerivAt_toLp 2 _
  have hcomp2 := htoLp.comp_hasDerivAt θ hvecD
  have hfun_eq : (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane) ∘
      (fun x : ℝ => (![Real.cos x, Real.sin x] : Fin 2 → ℝ)) = unitCircle := by
    funext x
    simp [unitCircle, Function.comp]
  rw [hfun_eq] at hcomp2
  have hval : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
      (![(-Real.sin θ), Real.cos θ] : Fin 2 → ℝ) = unitCircleDeriv θ := by
    show WithLp.toLp 2 (![(-Real.sin θ), Real.cos θ] : Fin 2 → ℝ) = unitCircleDeriv θ
    rfl
  rwa [hval] at hcomp2

/--
**No global scalar potential.** If `vortexVelocity2D = ∇φ` held on `puncturedPlane`
for some smooth `φ`, then `θ ↦ φ (unitCircle θ)` would be a real-valued function of
`θ` whose derivative equals `circulationIntegrand θ = 1` everywhere (chain rule plus
the Riesz/gradient inner-product identity). By the fundamental theorem of calculus
its integral over `[0, 2π]` would then equal `φ (unitCircle (2π)) - φ (unitCircle 0) = 0`
(the circle closes up), while direct computation gives `2π`. Since `2π ≠ 0`, no such
`φ` exists.
-/
theorem not_hasGlobalScalarPotential2D_vortexVelocity2D :
    ¬ HasGlobalScalarPotential2D puncturedPlane vortexVelocity2D := by
  rintro ⟨φ, hφ, hv⟩
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun θ => φ (unitCircle θ)) (1 : ℝ) θ := by
    intro θ
    have hmem : unitCircle θ ∈ puncturedPlane := unitCircle_ne_zero θ
    have hφat : DifferentiableAt ℝ φ (unitCircle θ) :=
      (hφ.differentiableOn (by simp)).differentiableAt
        (isOpen_puncturedPlane.mem_nhds hmem)
    have hcirc := hasDerivAt_unitCircle θ
    have hcomp := hφat.hasFDerivAt.comp_hasDerivAt θ hcirc
    have hfe : (φ ∘ unitCircle) = (fun θ => φ (unitCircle θ)) := rfl
    rw [hfe] at hcomp
    have hval : fderiv ℝ φ (unitCircle θ) (unitCircleDeriv θ) = 1 := by
      rw [← inner_gradient_left (f := φ) (x := unitCircle θ) (y := unitCircleDeriv θ),
        ← hv (unitCircle θ) hmem]
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      have hone := circulationIntegrand_eq_one θ
      simp only [circulationIntegrand, RCLike.inner_apply, RCLike.conj_to_real,
        mul_comm] at hone ⊢
      linarith [hone]
    rwa [hval] at hcomp
  have hFTC : ∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) =
      φ (unitCircle (2 * Real.pi)) - φ (unitCircle 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      intervalIntegrable_const
  have hψeq : unitCircle (2 * Real.pi) = unitCircle 0 := by
    simp [unitCircle, Real.cos_two_pi, Real.sin_two_pi]
  rw [hψeq, sub_self] at hFTC
  have h3 : ∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) = 2 * Real.pi := by
    rw [intervalIntegral.integral_const]; ring
  rw [h3] at hFTC
  exact vortex_circulation_ne_zero hFTC

def openObligation_knottedExteriorCirculation : String :=
  "BLOCKED: general 3D knotted-exterior circulation vs global scalar potential \
requires de Rham / homology infrastructure beyond the present Mathlib surface."

theorem circulation_witness_nonzero : ∃ Γ : ℝ, Γ ≠ 0 ∧ Γ = 2 * Real.pi :=
  ⟨2 * Real.pi, vortex_circulation_ne_zero, rfl⟩

end Euler.PotentialFlow
