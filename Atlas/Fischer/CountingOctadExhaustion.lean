import Atlas.Fischer.CountingOctadParameters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def countingOctad (p : CountingOctadParameters) : Octad :=
  ⟨support (countingOctadCode p).val,(octads_mem _).mpr
    ⟨countingOctadCode p,countingOctadCode_weight p,rfl⟩⟩

theorem countingOctad_word (p : CountingOctadParameters) :
    octadWord (countingOctad p)=countingOctadCode p := by
  apply Subtype.ext
  apply support_injective
  rw [octadWord_support]
  rfl

theorem countingOctad_surjective : Function.Surjective countingOctad := by
  intro O
  obtain ⟨⟨h,r,e⟩,he⟩ := golayEquiv.surjective (octadWord O)
  have hw : hammingNorm (golayEncoder (h,r,e))=8 := by
    have hh := congrArg (fun c : golay => hammingNorm c.val) he
    exact hh.trans (octadWord_weight O)
  have hbit : e=0 ∨ e=1 := by exact (show ∀ b : Bit, b=0 ∨ b=1 from by decide) e
  have finish (p : CountingOctadParameters) (hp : countingOctadRaw p=(h,r,e)) : countingOctad p=O := by
    apply octadWord_injective
    rw [countingOctad_word,countingOctadCode,hp,he]
  rcases hbit with rfl | rfl
  · have hwe : hammingNorm (c0Encoder (h,r))=8 := by
      simpa only [golayEncoder,LinearMap.coe_mk,AddHom.coe_mk,zero_smul,add_zero] using hw
    rcases hex_weights h with h0 | h4 | h6
    · have hh : h=0 := Subtype.ext (hammingNorm_eq_zero.mp h0)
      subst h
      exact ⟨Sum.inl ⟨r,hwe⟩,finish _ rfl⟩
    · exact ⟨Sum.inr (Sum.inl ⟨⟨h,h4⟩,⟨r,hwe⟩⟩),finish _ rfl⟩
    · have hh := c0_weight_six h h6 r
      omega
  · have hwo : hammingNorm (c0Encoder (h,r)+eta)=8 := by
      simpa only [golayEncoder,LinearMap.coe_mk,AddHom.coe_mk,one_smul] using hw
    exact ⟨Sum.inr (Sum.inr ⟨h,⟨r,hwo⟩⟩),finish _ rfl⟩

/-- Exact disjoint parametrization of the actual759 octads; all counts are reused
from the retained encoder fibers, rather than supplied as external certificates. -/
def countingOctadEquiv : CountingOctadParameters ≃ Octad :=
  Equiv.ofBijective countingOctad (by
    apply (Fintype.bijective_iff_surjective_and_card countingOctad).mpr
    refine ⟨countingOctad_surjective,?_⟩
    rw [← Nat.card_eq_fintype_card,countingOctadParameters_card,Fintype.card_coe,octads_card])

end Atlas.Fischer
