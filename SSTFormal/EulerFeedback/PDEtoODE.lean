import SSTFormal.EulerFeedback.EulerianTransfer
import Euler.CurlTransportAlgebra
import Euler.VorticityTransport

/-!
SST-FV03-B1: from incompressible Euler momentum to material-vorticity ODE.

Scope:
* The first theorem derives the spatial curl balance from genuine Euler
  momentum, incompressibility, and smooth velocity/pressure slices.
* The second and third use the explicit, ordinary calculus requirements:
  time differentiation commutes with curl; the joint derivative decomposes
  into its temporal and spatial parts; and a material curve solves X'=u(X).
* These are regularity hypotheses, not a claimed Euler solution construction.
No assumption is made about an endpoint t=T or finite-core knots.

Note: under `open scoped ContDiff`, the token `ω` denotes `ℕ∞`, so vorticity
fields are named `omega` (ASCII) rather than `ω`.
-/

noncomputable section

open Set EulerSmoothLimit EulerVectorCalculus EulerMeanCutoffCurl
open scoped Topology ContDiff

namespace SSTFormal.EulerFeedback

/-- Curl of the divergence-free Euler momentum equation, with pressure
    eliminated by the ordinary curl-gradient identity. -/
theorem euler_momentum_implies_curl_balance
    (u : Space → Space) (p : Space → ℝ) (du : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p)
    (hdiv : ∀ x, divergence u x = 0)
    (hEuler : du = fun y => -fderiv ℝ u y (u y) - gradient p y)
    (x : Space) :
    vectorCurl du x + fderiv ℝ (vectorCurl u) x (u x) =
      fderiv ℝ u x (vectorCurl u x) := by
  rw [hEuler]
  have h := EulerComparatorCurlTransport.vectorCurl_euler_rhs
    u p hu hp x (hdiv x)
  rw [h]
  abel

/-- Passage from the Euler PDE to the material vorticity RHS at a time
    slice. The hypothesis hcurlTime is precisely the temporal-curl
    commutation, which requires time-space regularity of the parent field. -/
theorem euler_momentum_implies_material_curl_rhs
    (u : Space → Space) (p : Space → ℝ)
    (du dω : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p)
    (hdiv : ∀ x, divergence u x = 0)
    (hEuler : du = fun y => -fderiv ℝ u y (u y) - gradient p y)
    (hcurlTime : ∀ x, dω x = vectorCurl du x)
    (x : Space) :
    dω x + fderiv ℝ (vectorCurl u) x (u x) =
      fderiv ℝ u x (vectorCurl u x) := by
  rw [hcurlTime x]
  exact euler_momentum_implies_curl_balance u p du hu hp hdiv hEuler x

/-- Joint chain rule on a genuine material path. The material PDE identity
    is visible as an explicit premise, never silently postulated as Euler. -/
theorem material_chain_rule_to_linear_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (omega : ℝ × E → E) (u : ℝ → E → E) (X : ℝ → E)
    (hωdiff : ∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ omega (t, X t))
    (hmaterial : ∀ t ∈ Ioo (0 : ℝ) T,
      fderiv ℝ omega (t, X t) (1, u t (X t)) =
        fderiv ℝ (u t) (X t) (omega (t, X t)))
    (hX : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt X (u t (X t)) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => omega (s, X s))
      (fderiv ℝ (u t) (X t) (omega (t, X t))) t := by
  have h := (hωdiff t ht).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hX t ht))
  simpa only [Function.comp_def, id_eq, hmaterial t ht] using h

/-- Full conditional bridge for a time-dependent smooth Euler field.
    hjoint is the chain-rule decomposition of the spacetime curl derivative.
    hcurlTime is curl/partial-time commutation. Neither is a stability cap. -/
theorem smooth_euler_material_vorticity_ode
    (T : ℝ)
    (u : ℝ → Space → Space) (p : ℝ → Space → ℝ)
    (du dω : ℝ → Space → Space)
    (omega : ℝ × Space → Space) (X : ℝ → Space)
    (hu : ∀ t ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (u t))
    (hp : ∀ t ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (p t))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      divergence (u t) x = 0)
    (hEuler : ∀ t ∈ Ioo (0 : ℝ) T,
      du t = fun y => -fderiv ℝ (u t) y (u t y) - gradient (p t) y)
    (hcurlTime : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      dω t x = vectorCurl (du t) x)
    (hωval : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      omega (t,x) = vectorCurl (u t) x)
    (hωdiff : ∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ omega (t, X t))
    (hjoint : ∀ t ∈ Ioo (0 : ℝ) T,
      fderiv ℝ omega (t, X t) (1, u t (X t)) =
        dω t (X t) +
          fderiv ℝ (vectorCurl (u t)) (X t) (u t (X t)))
    (hX : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt X (u t (X t)) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => omega (s, X s))
      (fderiv ℝ (u t) (X t) (omega (t, X t))) t := by
  apply material_chain_rule_to_linear_ode T omega u X hωdiff _ hX t ht
  intro s hs
  rw [hjoint s hs]
  have h := euler_momentum_implies_material_curl_rhs
    (u s) (p s) (du s) (dω s)
    (hu s hs) (hp s hs) (hdiv s hs)
    (hEuler s hs) (hcurlTime s hs) (X s)
  rw [h, hωval s hs (X s)]

end SSTFormal.EulerFeedback

#print axioms SSTFormal.EulerFeedback.euler_momentum_implies_curl_balance
#print axioms SSTFormal.EulerFeedback.euler_momentum_implies_material_curl_rhs
#print axioms SSTFormal.EulerFeedback.material_chain_rule_to_linear_ode
#print axioms SSTFormal.EulerFeedback.smooth_euler_material_vorticity_ode
