import Atlas.GroupTheory.CommutatorEquiv
import Atlas.Comparisons.Classical.Orthogonal
import Atlas.LinearGroups.Orthogonal.B2BinaryStructure

/-! # The binary B₂/C₂ derived comparison

The full binary groups have order 720. These maps restrict the already verified
B₂-to-C₂ isomorphism to their actual commutator subgroups, of order 360.
-/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open Atlas.Orthogonal

/-- The actual B₂/C₂ comparison restricted to the actual derived subgroups. -/
def b2BinaryDerivedEquivC2Derived :
    commutator (ProjectiveElementary (formB 2 (ZMod 2))) ≃*
      commutator (Atlas.Symplectic.PSp 2 (ZMod 2)) :=
  Atlas.GroupTheory.commutatorEquiv (Classical.b2EquivC2 (F := ZMod 2))

/-- The actual derived subgroup of C₂(2), transported to A₆ through binary B₂. -/
def c2BinaryDerivedEquivAlt6 :
    commutator (Atlas.Symplectic.PSp 2 (ZMod 2)) ≃* alternatingGroup (Fin 6) :=
  b2BinaryDerivedEquivC2Derived.symm.trans b2BinaryDerivedEquivAlternating

/-- Compatibility with the ambient B₂-to-C₂ isomorphism. -/
@[simp] theorem b2BinaryDerivedEquivC2Derived_coe
    (g : commutator (ProjectiveElementary (formB 2 (ZMod 2)))) :
    (b2BinaryDerivedEquivC2Derived g : Atlas.Symplectic.PSp 2 (ZMod 2)) =
      Classical.b2EquivC2 (g : ProjectiveElementary (formB 2 (ZMod 2))) := rfl

/-- The alternating comparison commutes with restriction of the B₂/C₂ comparison. -/
@[simp] theorem c2BinaryDerivedEquivAlt6_coherence
    (g : commutator (ProjectiveElementary (formB 2 (ZMod 2)))) :
    c2BinaryDerivedEquivAlt6 (b2BinaryDerivedEquivC2Derived g) =
      b2BinaryDerivedEquivAlternating g := by
  simp [c2BinaryDerivedEquivAlt6]
end Atlas.Comparisons.Exceptional
