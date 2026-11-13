import Euler.PotentialFlow.Circulation
import Euler.PotentialFlow.Laplace

/-!
# Vortex-core / exterior coupling interface

Research interface between a compact vortical core and an irrotational exterior
field. Helmholtz / Hodge-type splittings are recorded as **data+proof contracts**,
not as fully proved functional-analytic existence/uniqueness theorems.

SST notes (documentation only):
* Potential flow cannot replace internal vortex dynamics.
* An irrotational exterior does not imply vanishing circulation.
* A local potential need not be globally single-valued.
* Exterior-field structure is not a stability/persistence proof for a Ruban Trefoil.
* Ruban Trefoil geometry is deferred to a future adapter.
* No numerical validation is performed here.
-/

noncomputable section

open Set ContDiff InnerProductSpace Laplacian

namespace Euler.PotentialFlow

/--
Helmholtz / Hodge-style research decomposition contract:

`v = v_vortex + ∇φ + h`

where `h` is reserved for topology / boundary-driven harmonic fields.
Existence and uniqueness of such a splitting are **not** claimed; any supplied
components must satisfy the reconstruction identity on the exterior.
-/
structure HelmholtzHodgeInterface (D : Set Space) where
  /-- Compact core supporting vorticity. -/
  core : Set Space
  compact_core : IsCompact core
  /-- Exterior domain (typically `univ \ core`). -/
  exterior : Set Space := exteriorDomain core
  open_exterior : IsOpen exterior
  /-- Full velocity field. -/
  velocity : Space → Space
  /-- Core-supported vortical contribution (may already include Biot–Savart circulation). -/
  vortexPart : Space → Space
  /-- Scalar potential contribution on the exterior. -/
  scalarPotential : Space → ℝ
  /-- Harmonic / topology-driven remainder. -/
  harmonicPart : Space → Space
  /-- Mandatory pointwise reconstruction identity on the exterior. -/
  reconstruction :
    ∀ x ∈ exterior,
      velocity x =
        vortexPart x + potentialVelocity scalarPotential x + harmonicPart x

/--
Avoid double-counting: if `vortexPart` is already reconstructed from the full
vorticity distribution (e.g. Biot–Savart), it may already carry the circulation
around the core. Adding an independent circulatory harmonic field then overcounts.
This is a documentation predicate, not a proved uniqueness theorem.
-/
def NoDoubleCountingCaution {D : Set Space} (_I : HelmholtzHodgeInterface D) : String :=
  "If vortexPart already comes from full Biot-Savart reconstruction, do not add a \
second circulatory harmonic remainder that encodes the same core circulation."

private theorem divergence_add {u v : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    divergence (fun y => u y + v y) x = divergence u x + divergence v x := by
  simp only [divergence]
  rw [fderiv_fun_add hu hv]
  change (LinearMap.trace ℝ Space) (fderiv ℝ u x + fderiv ℝ v x).toLinearMap =
    (LinearMap.trace ℝ Space) (fderiv ℝ u x).toLinearMap +
      (LinearMap.trace ℝ Space) (fderiv ℝ v x).toLinearMap
  rw [ContinuousLinearMap.toLinearMap_add, map_add]

/--
Formal consequence of the reconstruction contract: under differentiability of each
summand (and `ContDiff ℝ ∞` of the scalar potential so that `∇·∇φ = Δφ`),

`∇ · v = ∇ · v_vortex + Δφ + ∇ · h`.
-/
theorem helmholtzHodge_divergence_of_reconstruction
    {D : Set Space} (I : HelmholtzHodgeInterface D) {x : Space} (hx : x ∈ I.exterior)
    (hφ : ContDiff ℝ ∞ I.scalarPotential)
    (hvort : DifferentiableAt ℝ I.vortexPart x)
    (hharm : DifferentiableAt ℝ I.harmonicPart x) :
    divergence I.velocity x =
      divergence I.vortexPart x + Δ I.scalarPotential x + divergence I.harmonicPart x := by
  have hgrad : DifferentiableAt ℝ (potentialVelocity I.scalarPotential) x :=
    ((contDiff_gradient I.scalarPotential hφ).differentiable (by simp)).differentiableAt
  have hsum₁ : DifferentiableAt ℝ
      (fun y => I.vortexPart y + potentialVelocity I.scalarPotential y) x :=
    hvort.add hgrad
  have hnear : I.velocity =ᶠ[nhds x]
      (fun y => I.vortexPart y + potentialVelocity I.scalarPotential y + I.harmonicPart y) := by
    filter_upwards [I.open_exterior.mem_nhds hx] with y hy
    exact I.reconstruction y hy
  have hdiff_rhs : DifferentiableAt ℝ
      (fun y => I.vortexPart y + potentialVelocity I.scalarPotential y + I.harmonicPart y) x :=
    hsum₁.add hharm
  have hfderiv :
      fderiv ℝ I.velocity x =
        fderiv ℝ (fun y =>
          I.vortexPart y + potentialVelocity I.scalarPotential y + I.harmonicPart y) x :=
    Filter.EventuallyEq.fderiv_eq hnear
  have hdiv_eq :
      divergence I.velocity x =
        divergence (fun y =>
          I.vortexPart y + potentialVelocity I.scalarPotential y + I.harmonicPart y) x := by
    simp only [divergence, hfderiv]
  have hdiv_split :
      divergence (fun y =>
          I.vortexPart y + potentialVelocity I.scalarPotential y + I.harmonicPart y) x =
        divergence I.vortexPart x + divergence (potentialVelocity I.scalarPotential) x +
          divergence I.harmonicPart x := by
    have h1 := divergence_add (u := fun y => I.vortexPart y + potentialVelocity I.scalarPotential y)
      (v := I.harmonicPart) hsum₁ hharm
    have h2 := divergence_add hvort hgrad
    rw [h1, h2, add_assoc]
  rw [hdiv_eq, hdiv_split, divergence_potentialVelocity_eq_laplacian I.scalarPotential hφ x]

/-- Coupling package between core vorticity support and exterior potential class. -/
structure VortexCoreCoupling (K : Set Space) (v : Space → Space) : Prop where
  split : VortexCoreExteriorSplit K v

/-- Future SST attachment points (documentation strings only). -/
def sstAttachment_framework : String :=
  "SST Falsifier Framework v1.1.2-CANONICAL_FROZEN (documentation attachment only)"

def sstAttachment_eulerTrajectoryGenerator : String :=
  "Euler Trajectory Generator v0.4.0 (documentation attachment only)"

def sstAttachment_rubanTrefoil : String :=
  "Ruban Trefoil seed geometry deferred to a separate geometry adapter"

def sstAttachment_numericalPaths : String :=
  "Future independent numerical paths: Python/C++ and Intel Arc/NVIDIA CUDA \
(not executed in this formal module)"

/--
Proved coupling lemma available now: an exterior potential class yields
irrotationality on the exterior domain. No Hodge existence is claimed.
-/
theorem coupling_exterior_irrotational
    {K : Set Space} {v : Space → Space}
    (h : VortexCoreCoupling K v) :
    IsIrrotationalOn (exteriorDomain K) v :=
  h.split.exterior.irrotational

/--
Open obligation: construct a true Hodge decomposition on `exteriorDomain K`
with controlled harmonic dimension determined by topology.
-/
def openObligation_hodgeDecomposition : String :=
  "UNRESOLVED: full Hodge / Helmholtz decomposition on knotted exteriors is an \
interface only; functional-analytic hypotheses are not available in-tree."

end Euler.PotentialFlow
