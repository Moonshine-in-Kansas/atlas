import Atlas.Fischer.CubicColumnPairTransport
import Atlas.Fischer.CubicTrioNeighborCounts

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

 theorem cubicDisjointColumnRepresentation (D H F : Octad) (i j k : HexIndex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hD : D.val = tetrad i ∪ tetrad j) (hH : H.val = tetrad i ∪ tetrad k)
    (hDF : (D.val ∩ F.val).card = 0) (hHF : (H.val ∩ F.val).card = 4) :
    ∃ l : HexIndex, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ F.val = tetrad k ∪ tetrad l := by
  let t := countingSourceOctadEquiv.symm F
  have ht : countingSourceOctadEquiv t = F := Equiv.apply_symm_apply _ F
  have hI : hexIndexEquiv i ≠ hexIndexEquiv j := fun h => hij (hexIndexEquiv.injective h)
  have hJ : hexIndexEquiv i ≠ hexIndexEquiv k := fun h => hik (hexIndexEquiv.injective h)
  have hK : hexIndexEquiv j ≠ hexIndexEquiv k := fun h => hjk (hexIndexEquiv.injective h)
  have hp : (countingSourceColumn t (hexIndexEquiv i)).card +
      (countingSourceColumn t (hexIndexEquiv j)).card = 0 ∧
      (countingSourceColumn t (hexIndexEquiv i)).card +
      (countingSourceColumn t (hexIndexEquiv k)).card = 4 := by
    rw [hD,← ht,cubicCommonNeighbor_two_column_card _ i j hij,
      cubicCommonNeighbor_column_card,cubicCommonNeighbor_column_card] at hDF
    rw [hH,← ht,cubicCommonNeighbor_two_column_card _ i k hik,
      cubicCommonNeighbor_column_card,cubicCommonNeighbor_column_card] at hHF
    exact ⟨hDF,hHF⟩
  let q : CubicSourcePairNeighbors (hexIndexEquiv i) (hexIndexEquiv j) (hexIndexEquiv k) 0 4 := ⟨t,hp⟩
  let u := cubicSourceMixedEquiv _ _ _ hI hJ hK q
  obtain ⟨l,hl⟩ := (cubicSourceCommonFourEquiv (hexIndexEquiv k) (hexIndexEquiv i)
    (hexIndexEquiv j) (Ne.symm hJ) (Ne.symm hK) hI).surjective u
  have he : (Sum.inl (⟨{hexIndexEquiv k,l.val},Finset.card_pair (Ne.symm l.property.1)⟩ : CountingSourceTypeA)
      : CountingSourceParameters) = t := congrArg Subtype.val hl
  refine ⟨hexPos l.val,?_,?_,?_,?_⟩
  · intro h
    exact l.property.2.1 (by have hh := congrArg hexIndexEquiv h; simpa [hexPos] using hh)
  · intro h
    exact l.property.2.2 (by have hh := congrArg hexIndexEquiv h; simpa [hexPos] using hh)
  · intro h
    exact l.property.1 (by have hh := congrArg hexIndexEquiv h; simpa [hexPos] using hh)
  · rw [← ht,← he]
    change (countingColumnPairOctad (hexIndexEquiv k) l.val (Ne.symm l.property.1)).val = _
    rw [countingColumnPairOctad_val,hexPos_index]

/-- An actual common four-neighbor supplies a refining sextet for any disjoint
pair; the verified source profile forces its remaining two columns. -/
theorem cubicDisjointPair_column_normalize (D F : Octad) (hDF : (D.val ∩ F.val).card = 0) :
    ∃ g : Mathieu24CodeModel,∃ i j k l : HexIndex,
      i ≠ j ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l ∧
      (g • D).val = tetrad i ∪ tetrad j ∧ (g • F).val = tetrad k ∪ tetrad l := by
  have hc := cubicPairIntersection_disjoint_bothFour D F hDF
  have hp : 0 < Fintype.card (CubicPairIntersectionFibre D F 4 4) := by
    rw [← Nat.card_eq_fintype_card,hc]
    decide
  obtain ⟨H⟩ := Fintype.card_pos_iff.mp hp
  obtain ⟨g,i,j,k,hij,hik,hjk,hD,hH⟩ := cubicCommonNeighbor_pair_normalize D H.val H.property.1
  obtain ⟨l,hli,hlj,hlk,hF⟩ := cubicDisjointColumnRepresentation (g • D) (g • H.val) (g • F)
    i j k hij hik hjk hD hH
    ((cubicCommonNeighbor_pair_card g D F).trans hDF)
    (by rw [cubicCommonNeighbor_pair_card,Finset.inter_comm]; exact H.property.2)
  exact ⟨g,i,j,k,l,hij,Ne.symm hik,Ne.symm hjk,hli,hlj,Ne.symm hlk,hD,hF⟩

end Atlas.Fischer
