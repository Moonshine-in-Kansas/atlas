import Atlas.Conway.EisensteinFramePartition
import Atlas.Conway.EisensteinNineSignExclusions

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local irreducible] eisensteinNineHexadFamily

/-- Every actual constant norm-nine frame lies in the counted family of its intrinsic sign. -/
theorem eisensteinNineSignFrame_mem_family (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : EisensteinNineSignFrame b F) :
    F ∈ eisensteinNineHexadFamily b hb := by
  rcases eisensteinFrame_other_or_nine F with ⟨i,hi3,hi4,hi⟩ | h | h
  · exact (eisensteinNineSignFrame_not_other b hb F hF i hi3 hi4 hi).elim
  · have he := eisensteinNineSignFrame_unique b 1 F hF
      (eisensteinNineHexadFamily_sign 1 (by decide) F h)
    subst b
    exact h
  · have he := eisensteinNineSignFrame_unique b 2 F hF
      (eisensteinNineHexadFamily_sign 2 (by decide) F h)
    subst b
    exact h

/-- Intrinsic classification of each2673 family, independent of all canonical representative choices. -/
theorem eisensteinNineHexadFamily_mem_iff_sign (b : ZMod 3) (hb : b≠0) (F : EisensteinFrame) :
    F ∈ eisensteinNineHexadFamily b hb ↔ EisensteinNineSignFrame b F :=
  ⟨eisensteinNineHexadFamily_sign b hb F,eisensteinNineSignFrame_mem_family b hb F⟩

/-- Every explicit choice of constant hexad, inside phase coordinate and outside heavy
coordinate belongs to the same completed intrinsic2673 family of the indicated sign. -/
theorem eisensteinNineHexadFrame_mem_family (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) :
    eisensteinNineHexadFrame s hs k j hk hj b hb ∈ eisensteinNineHexadFamily b hb :=
  eisensteinNineSignFrame_mem_family b hb _ (eisensteinNineHexadFrame_sign s hs k j hk hj b hb)

end Atlas.Conway
