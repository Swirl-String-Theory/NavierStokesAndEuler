import Euler.PotentialFlow.Definitions

/-!
# Exterior fluid domain outside a compact vortex core

Defines `D = ℝ³ \ K` for a compact/closed core `K`, with explicit openness,
and treats connectedness / simple connectedness as hypotheses rather than
automatic consequences of knotted geometry.
-/

noncomputable section

open Set Topology ContDiff

namespace Euler.PotentialFlow

/-- Exterior of a core set `K`. -/
def exteriorDomain (K : Set Space) : Set Space :=
  (univ : Set Space) \ K

theorem exteriorDomain_eq (K : Set Space) :
    exteriorDomain K = Kᶜ := by
  simp [exteriorDomain, compl_eq_univ_sdiff]

theorem isOpen_exteriorDomain {K : Set Space} (hK : IsClosed K) :
    IsOpen (exteriorDomain K) := by
  simpa [exteriorDomain_eq] using hK.isOpen_compl

theorem isOpen_exteriorDomain_of_isCompact {K : Set Space} (hK : IsCompact K) :
    IsOpen (exteriorDomain K) :=
  isOpen_exteriorDomain hK.isClosed

/--
Connectedness of the exterior is an explicit hypothesis. A knotted compact
core in `ℝ³` typically leaves a connected but not simply connected exterior;
simple connectedness is never inferred from compactness alone.
-/
structure ExteriorDomainData (K : Set Space) : Prop where
  compact_core : IsCompact K
  preconnected_exterior : IsPreconnected (exteriorDomain K)

theorem ExteriorDomainData.open_exterior {K : Set Space}
    (h : ExteriorDomainData K) : IsOpen (exteriorDomain K) :=
  isOpen_exteriorDomain_of_isCompact h.compact_core

/-- Membership characterization. -/
theorem mem_exteriorDomain {K : Set Space} {x : Space} :
    x ∈ exteriorDomain K ↔ x ∉ K := by
  simp [exteriorDomain]

/--
Boundary regularity interface. No claim is made that every compact set admits
a classical smooth boundary; a geometry adapter may supply charts later.
-/
structure ExteriorBoundaryData (K : Set Space) where
  frontier_subset_closure : frontier K ⊆ closure K := by
    intro x hx
    exact frontier_subset_closure hx

/-- Exterior velocity regularity package. -/
structure ExteriorVelocityField (K : Set Space) (v : Space → Space) : Prop where
  open_exterior : IsOpen (exteriorDomain K)
  smooth_on_exterior : ContDiffOn ℝ ∞ v (exteriorDomain K)

/-- Irrotational exterior field. -/
structure IrrotationalExterior (K : Set Space) (v : Space → Space) : Prop
    extends ExteriorVelocityField K v where
  irrotational : IsIrrotationalOn (exteriorDomain K) v

/-- Incompressible exterior field. -/
structure IncompressibleExterior (K : Set Space) (v : Space → Space) : Prop
    extends ExteriorVelocityField K v where
  div_free : ∀ x ∈ exteriorDomain K, divergence v x = 0

/-- Combined exterior class: smooth, irrotational, and divergence-free on `ℝ³ \ K`. -/
structure ExteriorPotentialClass (K : Set Space) (v : Space → Space) : Prop where
  open_exterior : IsOpen (exteriorDomain K)
  smooth_on_exterior : ContDiffOn ℝ ∞ v (exteriorDomain K)
  irrotational : IsIrrotationalOn (exteriorDomain K) v
  div_free : ∀ x ∈ exteriorDomain K, divergence v x = 0

/-- Compact core supporting vorticity, with an irrotational incompressible exterior. -/
structure VortexCoreExteriorSplit (K : Set Space) (v : Space → Space) : Prop where
  compact_core : IsCompact K
  exterior : ExteriorPotentialClass K v

/--
**Non-claim (documentation):** `IrrotationalExterior` does not entail
`HasGlobalScalarPotential` on `exteriorDomain K`. A concrete 2D obstruction
is formalized in `Circulation.lean`.
-/
theorem exterior_potential_class_implies_irrotational
    {K : Set Space} {v : Space → Space}
    (h : ExteriorPotentialClass K v) : IsIrrotationalOn (exteriorDomain K) v :=
  h.irrotational

end Euler.PotentialFlow
