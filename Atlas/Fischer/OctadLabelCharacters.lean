import Atlas.Fischer.OctadEvenRestriction
import Atlas.Fischer.OctadCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual cocode pairing factors through octad restriction precisely on N_O. -/
def octadLabelCharacter (O : Octad) (d : octadCocodeAnnihilator O) :
    Module.Dual Bit (octadEvenCode O) :=
  ((octadShortenedCode O).liftQ (cocodeDualEquiv d.val) (by
    intro c hc
    exact (mem_octadCocodeAnnihilator O d.val).mp d.prop ⟨c, hc⟩)).comp
      (octadShortenedQuotientEquiv O).symm.toLinearMap

theorem octadLabelCharacter_restriction (O : Octad) (d : octadCocodeAnnihilator O)
    (c : golay) :
    octadLabelCharacter O d (octadEvenRestriction O c) = cocodePairing c d.val := by
  unfold octadLabelCharacter
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have he : (octadShortenedQuotientEquiv O).symm (octadEvenRestriction O c) =
      Submodule.Quotient.mk c := by
    apply (octadShortenedQuotientEquiv O).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- Independence of the Golay representative is a consequence, not an assumption. -/
theorem octadLabelCharacter_independent (O : Octad) (d : octadCocodeAnnihilator O)
    (c e : golay) (h : octadEvenRestriction O c = octadEvenRestriction O e) :
    cocodePairing c d.val = cocodePairing e d.val := by
  rw [← octadLabelCharacter_restriction O d c,
    ← octadLabelCharacter_restriction O d e, h]

end Atlas.Fischer
