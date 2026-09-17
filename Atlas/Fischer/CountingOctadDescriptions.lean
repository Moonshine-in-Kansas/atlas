import Atlas.Fischer.CountingOctadMasks
import Atlas.Fischer.CountingOctadExhaustion
import Atlas.Fischer.CountingHexacodeWeights

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem countingPointCoordinates_letter_iff (w : HexWord) (p : Omega) :
    (countingPointCoordinates p).2 = countingHexCoordinates w (countingPointCoordinates p).1 ↔
      countingRowLetter p.2=w p.1 := by
  change countingLetterEquiv (countingHexLocal (hexIndexEquiv p.1) (countingRowLetter p.2)) =
    countingLetterEquiv (countingHexLocal (hexIndexEquiv p.1) (w (hexPos (hexIndexEquiv p.1)))) ↔ _
  rw [hexPos_index,countingLetterEquiv.injective.eq_iff,(countingHexLocal _).injective.eq_iff]

theorem countingPointCoordinates_zero_iff (p : Omega) :
    (countingPointCoordinates p).2=0 ↔ countingRowLetter p.2=0 := by
  change countingLetterEquiv (countingHexLocal (hexIndexEquiv p.1) (countingRowLetter p.2))=0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff,LinearEquiv.map_eq_zero_iff]

theorem countingHexCoordinates_zero_iff (w : HexWord) (p : Omega) :
    countingHexCoordinates w (countingPointCoordinates p).1=0 ↔ w p.1=0 := by
  change countingLetterEquiv (countingHexLocal (hexIndexEquiv p.1)
    (w (hexPos (hexIndexEquiv p.1))))=0 ↔ _
  rw [hexPos_index,LinearEquiv.map_eq_zero_iff,LinearEquiv.map_eq_zero_iff]

/-- TypeA is literally the union of the two complete columns in its mask. -/
theorem countingTypeA_membership (t : CountingTypeA) (p : Omega) :
    p ∈ (countingOctad (Sum.inl t)).val ↔
      (countingPointCoordinates p).1 ∈ support t.val.val := by
  change p ∈ support (golayEncoder (0,t.val,0)) ↔ _
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and]
  simp [golayEncoder,c0Encoder,jWord,rho,support,countingPointCoordinates]

/-- TypeB uses the exact source pair {0,h_i}, complemented according to an even mask. -/
theorem countingTypeB_membership (t : CountingTypeB) (p : Omega) :
    p ∈ (countingOctad (Sum.inr (Sum.inl t))).val ↔
      countingHexCoordinates t.1.val.val (countingPointCoordinates p).1 ≠ 0 ∧
      if countingPairMask t.1.val t.2.val (countingPointCoordinates p).1=0 then
        ((countingPointCoordinates p).2=0 ∨
          (countingPointCoordinates p).2=countingHexCoordinates t.1.val.val (countingPointCoordinates p).1)
      else ((countingPointCoordinates p).2≠0 ∧
          (countingPointCoordinates p).2≠countingHexCoordinates t.1.val.val (countingPointCoordinates p).1) := by
  simp only [ne_eq,countingHexCoordinates_zero_iff,countingPointCoordinates_zero_iff,
    countingPointCoordinates_letter_iff]
  change p ∈ support (golayEncoder (t.1.val,t.2.val,0)) ↔ _
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [golayEncoder,LinearMap.coe_mk,AddHom.coe_mk,zero_smul,add_zero]
  change j (t.1.val.val p.1) p.2+t.2.val.val (hexIndexEquiv p.1) ≠ 0 ↔ _
  by_cases hh : t.1.val.val p.1=0
  · have hr := countingTypeB_zero_off_support t (hexIndexEquiv p.1) (by simpa only [hexPos_index] using hh)
    simp [hh,hr]
  · rw [counting_even_column _ _ _ hh]
    have he : countingPairMask t.1.val t.2.val (countingPointCoordinates p).1 =
      t.2.val.val (hexIndexEquiv p.1)+qK (t.1.val.val p.1) := by
      change t.2.val.val (hexIndexEquiv p.1)+qK (t.1.val.val (hexPos (hexIndexEquiv p.1))) = _
      rw [hexPos_index]
    rw [he]
    by_cases hm : t.2.val.val (hexIndexEquiv p.1)+qK (t.1.val.val p.1)=0 <;>
      by_cases h0 : countingRowLetter p.2=0 <;> by_cases hu : countingRowLetter p.2=t.1.val.val p.1 <;>
      simp [hh,hm,h0,hu]

/-- TypeC consists of five source singletons and the complementary triple in its
unique distinguished column. -/
theorem countingTypeC_membership (t : CountingTypeC) (p : Omega) :
    p ∈ (countingOctad (Sum.inr (Sum.inr t))).val ↔
      if (countingPointCoordinates p).1=countingDistinguishedColumn t then
        (countingPointCoordinates p).2 ≠ countingHexCoordinates t.1.val (countingPointCoordinates p).1
      else (countingPointCoordinates p).2 = countingHexCoordinates t.1.val (countingPointCoordinates p).1 := by
  simp only [ne_eq,countingPointCoordinates_letter_iff]
  change p ∈ support (golayEncoder (t.1,t.2.val,1)) ↔ _
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [golayEncoder,LinearMap.coe_mk,AddHom.coe_mk,one_smul]
  change j (t.1.val p.1) p.2+t.2.val.val (hexIndexEquiv p.1)+eta p ≠ 0 ↔ _
  rw [counting_odd_column]
  have hm : t.2.val.val (hexIndexEquiv p.1)+qK (t.1.val p.1)+
      (if hexIndexEquiv p.1=5 then 1 else 0)=
      (Pi.single (countingDistinguishedColumn t) (1 : Bit) : Fin 6 → Bit) (hexIndexEquiv p.1) := by
    have h := congrFun (countingDistinguishedColumn_mask t) (hexIndexEquiv p.1)
    simpa only [countingOddMask,Pi.add_apply,oddMask,Equiv.symm_apply_apply,add_assoc] using h
  rw [hm]
  change _ ↔ if hexIndexEquiv p.1=countingDistinguishedColumn t then _ else _
  by_cases hc : hexIndexEquiv p.1=countingDistinguishedColumn t <;>
    by_cases hr : countingRowLetter p.2=t.1.val p.1 <;> simp [Pi.single_apply,hc,hr]

end Atlas.Fischer
