import Atlas.Rudvalis.GaussianLatticeFinite
import Atlas.Rudvalis.SecondFrameLineReflections
import Atlas.Rudvalis.SecondFrameGlueEmbedding
import Atlas.Rudvalis.SeedFrobeniusOrder

namespace Atlas.Rudvalis

theorem distinguishedReflection_lattice_iff (v : RationalSpace) :
    distinguishedReflection v∈rudvalisLattice ↔ v∈rudvalisLattice :=
  distinguishedReflection_lattice_of_glue_embedding secondFrameGlue_embedding v

theorem secondFrameLineReflection_lattice_iff (a : Point) (v : RationalSpace) :
    secondFrameLineReflection a v∈rudvalisLattice ↔ v∈rudvalisLattice :=
  secondFrameLineReflection_lattice_of_glue_embedding secondFrameGlue_embedding a v

/-- The actual distinguished Gaussian lattice reflection, constructed through binary glue. -/
noncomputable def rudvalisReflection : gaussianLatticeGroup :=
  ⟨distinguishedReflection,distinguishedReflection_pairing,
    fun v => (distinguishedReflection_lattice_iff v).symm,distinguishedReflection_gaussian⟩

noncomputable def secondFrameLineIsometry (a : Point) : gaussianLatticeGroup :=
  ⟨secondFrameLineReflection a,secondFrameLineReflection_pairing a,
    fun v => (secondFrameLineReflection_lattice_iff a v).symm,secondFrameLineReflection_gaussian a⟩

theorem rudvalisReflection_order : orderOf rudvalisReflection=2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact distinguishedReflection_involutive v
  · intro h
    exact distinguishedReflection_ne_one (congrArg Subtype.val h)

end Atlas.Rudvalis
