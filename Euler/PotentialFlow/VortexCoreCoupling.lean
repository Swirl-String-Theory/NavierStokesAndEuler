import Euler.PotentialFlow.Circulation

/-!
# Vortex-core / exterior coupling interface

Research interface between a compact vortical core and an irrotational exterior
field. Helmholtz / Hodge-type splittings are recorded as **interfaces**, not as
fully proved functional-analytic theorems.

SST notes (documentation only):
* Potential flow cannot replace internal vortex dynamics.
* An irrotational exterior does not imply vanishing circulation.
* A local potential need not be globally single-valued.
* Exterior-field structure is not a stability/persistence proof for a Ruban Trefoil.
* Ruban Trefoil geometry is deferred to a future adapter.
* No numerical validation is performed here.
-/

noncomputable section

open Set ContDiff

namespace Euler.PotentialFlow

/--
Helmholtz / Hodge-style research decomposition

`v = v_vortex + ∇φ + h`

where `h` is reserved for topology / boundary-driven harmonic fields.
This is an interface, not a proved existence/uniqueness theorem.
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
  /-- Optional local scalar potential on the exterior. -/
  hasScalarPotential : Prop := False
  /-- Optional harmonic remainder required by topology / boundary conditions. -/
  hasHarmonicRemainder : Prop := False
  /-- Pointwise reconstruction identity on the exterior, when witnesses are supplied. -/
  reconstruction : Prop := True

/--
Avoid double-counting: if `vortexPart` is already reconstructed from the full
vorticity distribution (e.g. Biot–Savart), it may already carry the circulation
around the core. Adding an independent circulatory harmonic field then overcounts.
This is a documentation predicate, not a proved uniqueness theorem.
-/
def NoDoubleCountingCaution {D : Set Space} (_I : HelmholtzHodgeInterface D) : String :=
  "If vortexPart already comes from full Biot-Savart reconstruction, do not add a \
second circulatory harmonic remainder that encodes the same core circulation."

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

/-- Explicit non-claims retained for scientific hygiene. -/
structure PotentialFlowNonClaims : Prop where
  no_replace_core_dynamics : True := trivial
  no_automatic_zero_circulation : True := trivial
  no_automatic_global_potential : True := trivial
  no_trefoil_stability_proof : True := trivial

theorem potentialFlowNonClaims : PotentialFlowNonClaims := {}

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
