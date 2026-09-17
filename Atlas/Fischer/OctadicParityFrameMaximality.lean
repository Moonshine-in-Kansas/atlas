import Atlas.Fischer.OctadicParityFrames
import Atlas.GroupTheory.CommutingFrameExtension
import Mathlib.Data.Set.Card

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem distinguished_pairing_one_commute (s t : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector s) (reflectingRootParameterVector t)=1) :
    Commute (distinguishedRootElement s) (distinguishedRootElement t) := by
  have hc := displayedRootRay_unit_commute s t (by rw [h]; norm_num)
  change distinguishedRootElement s * distinguishedRootElement t = _
  apply Subtype.ext
  exact hc

theorem octadicParityFrame_commuting (O : Octad) (e : Bit) :
    ∀ x ∈ octadicParityFrame O e, ∀ y ∈ octadicParityFrame O e, Commute x y := by
  rintro x ⟨i | χ,rfl⟩ y ⟨j | ψ,rfl⟩
  · by_cases h : i.val=j.val
    · have h' : i=j := Subtype.ext h
      subst j
      exact Commute.refl _
    · apply distinguished_pairing_one_commute
      change hermitian (basicAxis i.val) (basicAxis j.val)=1
      rw [hermitian_basicAxis_basicAxis,if_neg h]
  · apply distinguished_pairing_one_commute
    change hermitian (basicAxis i.val) (octadicRoot (chosenOctadCalibration O) ψ.val)=1
    rw [hermitian_basicAxis_octadic,if_pos i.prop]
  · apply Commute.symm
    apply distinguished_pairing_one_commute
    change hermitian (basicAxis j.val) (octadicRoot (chosenOctadCalibration O) χ.val)=1
    rw [hermitian_basicAxis_octadic,if_pos j.prop]
  · by_cases h : χ.val=ψ.val
    · have h' : χ=ψ := Subtype.ext h
      subst ψ
      exact Commute.refl _
    · apply distinguished_pairing_one_commute
      change hermitian (octadicRoot (chosenOctadCalibration O) χ.val)
        (octadicRoot (chosenOctadCalibration O) ψ.val)=1
      rw [octadicRoot_pairing,if_neg h,if_pos (χ.prop.trans ψ.prop.symm)]

/-- Each parity class gives a genuine maximal frame, without a group-order premise. -/
theorem octadicParityFrame_isFrame (O : Octad) (e : Bit) :
    IsFischerFrame (octadicParityFrame O e) := by
  obtain ⟨F,hF,hsub⟩ := Atlas.GroupTheory.exists_commutingFrame_containing
    (Set.range distinguishedRootElement) (octadicParityFrame O e)
    (by rintro x ⟨t,rfl⟩; exact ⟨_,rfl⟩) (octadicParityFrame_commuting O e)
  have he : octadicParityFrame O e=F := Set.eq_of_subset_of_ncard_le hsub (by
    change Nat.card F ≤ Nat.card (octadicParityFrame O e)
    rw [fischerFrame_card F hF,octadicParityFrame_card]) (Set.toFinite F)
  exact he.symm ▸ hF

end Atlas.Fischer
