import Atlas.Rudvalis.SeedSignedOperators
import Atlas.Codes.QuaternaryLayers
import Mathlib.Algebra.Module.ZMod

/-! The literal Version 33 quaternary code: doubled torsion plus signed seed orbit. -/
namespace Atlas.Rudvalis

abbrev QuaternaryWord := Coordinate → ZMod 4

noncomputable def quaternarySeed (z : SeedOrbitIndex) : QuaternaryWord :=
  fun q => (seedOrbitWord z q : ZMod 4)

noncomputable def quaternaryEvenLayer : Submodule (ZMod 4) QuaternaryWord :=
  AddSubgroup.toZModSubmodule 4
    (binaryTorsion.toAddSubgroup.map Atlas.Codes.Quaternary.double)

noncomputable def quaternarySeedSpan : Submodule (ZMod 4) QuaternaryWord :=
  Submodule.span (ZMod 4) (Set.range quaternarySeed)

/-- Exactly the defining sum in Version 33, equation `eq:seedcode`. -/
noncomputable def quaternaryCode : Submodule (ZMod 4) QuaternaryWord :=
  quaternaryEvenLayer ⊔ quaternarySeedSpan

theorem quaternaryEvenLayer_mem (w : QuaternaryWord) :
    w∈quaternaryEvenLayer ↔ ∃ b : BinaryWord,
      b∈binaryTorsion ∧ Atlas.Codes.Quaternary.double b=w := Iff.rfl

theorem quaternaryCode_double (b : BinaryWord) (hb : b∈binaryTorsion) :
    Atlas.Codes.Quaternary.double b∈quaternaryCode :=
  (show quaternaryEvenLayer ≤ quaternaryCode from le_sup_left)
    ((quaternaryEvenLayer_mem _).mpr ⟨b,hb,rfl⟩)

theorem quaternaryCode_seed (z : SeedOrbitIndex) : quaternarySeed z∈quaternaryCode :=
  (show quaternarySeedSpan ≤ quaternaryCode from le_sup_right)
    (Submodule.subset_span ⟨z,rfl⟩)

theorem quaternaryCode_le (Q : Submodule (ZMod 4) QuaternaryWord)
    (heven : ∀ b : BinaryWord, b∈binaryTorsion → Atlas.Codes.Quaternary.double b∈Q)
    (hseed : ∀ z : SeedOrbitIndex, quaternarySeed z∈Q) : quaternaryCode≤Q := by
  apply sup_le
  · rintro w ⟨b,hb,rfl⟩
    exact heven b hb
  · apply Submodule.span_le.mpr
    rintro w ⟨z,rfl⟩
    exact hseed z

theorem quaternaryEvenLayer_reduce (w : QuaternaryWord) (hw : w ∈ quaternaryEvenLayer) :
    Atlas.Codes.Quaternary.reduce w=0 := by
  obtain ⟨b,hb,rfl⟩ := (quaternaryEvenLayer_mem w).mp hw
  exact Atlas.Codes.Quaternary.reduce_double b

theorem quaternarySeed_reduce (z : SeedOrbitIndex) :
    Atlas.Codes.Quaternary.reduce (quaternarySeed z)=
      (fun q => (seedOrbitWord z q : Bit)) := by
  funext q
  change Atlas.Codes.Quaternary.reduceScalar (seedOrbitWord z q : ZMod 4)=_
  exact map_intCast _ _

end Atlas.Rudvalis
