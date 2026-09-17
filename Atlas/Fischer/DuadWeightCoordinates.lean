import Atlas.Fischer.DuadShortenedCode
import Atlas.Fischer.OctadShortenedDivisibility
import Atlas.Fischer.CoordinateEvaluation

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Recover the actual octad from an actual weight-eight Golay word. -/
def golayOctadOfWeight (c : golay) (hc : hammingNorm c.val=8) : Octad :=
  ⟨support c.val,(octads_mem _).mpr ⟨c,hc,rfl⟩⟩

theorem golayOctadOfWeight_word (c : golay) (hc : hammingNorm c.val=8) :
    octadWord (golayOctadOfWeight c hc)=c := by
  apply Subtype.ext
  apply support_injective
  exact octadWord_support _

theorem mem_duadShortenedCode_support (p : Finset Omega) (c : golay) :
    c ∈ duadShortenedCode p ↔ Disjoint p (support c.val) := by
  rw [mem_duadShortenedCode,Finset.disjoint_left]
  simp [support]

/-- Weight-eight shortened words are literally octads avoiding the duad. -/
def duadWeightEightEquiv (p : Finset Omega) :
    {c : duadShortenedCode p // hammingNorm c.val.val=8} ≃
      {O : Octad // Disjoint p O.val} where
  toFun c := ⟨golayOctadOfWeight c.val.val c.property,
    (mem_duadShortenedCode_support p c.val.val).mp c.val.property⟩
  invFun O := ⟨⟨octadWord O.val,by
    rw [mem_duadShortenedCode_support,octadWord_support]
    exact O.property⟩,octadWord_weight O.val⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact golayOctadOfWeight_word c.val.val c.property
  right_inv O := by
    apply Subtype.ext
    apply Subtype.ext
    exact octadWord_support O.val

theorem golayComplement_weight_sixteen (c : golay) (hc : hammingNorm c.val=16) :
    hammingNorm (c+golayOne).val=8 := by
  have h := complement_weight c.val
  rw [hc] at h
  change hammingNorm (c.val+allOnes)=8
  omega

/-- Weight-sixteen shortened words are complements of octads containing the duad. -/
def duadWeightSixteenEquiv (p : Finset Omega) :
    {c : duadShortenedCode p // hammingNorm c.val.val=16} ≃
      {O : Octad // p ⊆ O.val} where
  toFun c := by
    let d : golay := c.val.val+golayOne
    have hd : hammingNorm d.val=8 := by
      have h := complement_weight c.val.val.val
      rw [c.property] at h
      change hammingNorm (c.val.val.val+allOnes)=8
      omega
    refine ⟨golayOctadOfWeight d hd,?_⟩
    intro i hi
    have hz := (mem_duadShortenedCode p c.val.val).mp c.val.property i hi
    change i ∈ support d.val
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change c.val.val.val i+1 ≠ 0
    rw [hz,zero_add]
    exact one_ne_zero
  invFun O := ⟨⟨octadComplementWord O.val,by
    rw [mem_duadShortenedCode]
    intro i hi
    simp [octadComplementWord_apply,O.property hi]⟩,octadComplementWord_weight O.val⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    change golayOne+octadWord (golayOctadOfWeight (c.val.val+golayOne) (golayComplement_weight_sixteen c.val.val c.property))=c.val.val
    rw [golayOctadOfWeight_word]
    calc
      _ = c.val.val+(golayOne+golayOne) := by abel
      _ = _ := by rw [parkerGolay_add_self,add_zero]
  right_inv O := by
    apply Subtype.ext
    apply octadWord_injective
    change octadWord (golayOctadOfWeight (octadComplementWord O.val+golayOne) (golayComplement_weight_sixteen _ (octadComplementWord_weight O.val)))=octadWord O.val
    rw [golayOctadOfWeight_word]
    change (golayOne+octadWord O.val)+golayOne=octadWord O.val
    calc
      _ = octadWord O.val+(golayOne+golayOne) := by abel
      _ = _ := by rw [parkerGolay_add_self,add_zero]

end Atlas.Fischer
