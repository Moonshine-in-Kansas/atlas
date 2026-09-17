import Atlas.Fischer.CubicCommonNeighborTransport
import Atlas.Fischer.CountingSourceColumns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def cubicSourceCommonCondition (i j k : Fin 6) (u : ℕ) (t : CountingSourceParameters) : Prop :=
    (countingSourceColumn t i).card+(countingSourceColumn t j).card=4 ∧
    (countingSourceColumn t i).card+(countingSourceColumn t k).card=4 ∧
    (countingSourceColumn t i).card=u

abbrev CubicSourceCommonNeighbors (i j k : Fin 6) (u : ℕ) :=
  {t : CountingSourceParameters // cubicSourceCommonCondition i j k u t}

theorem cubicCommonNeighbor_column_card (t : CountingSourceParameters) (i : HexIndex) :
    ((countingSourceOctadEquiv t).val ∩ tetrad i).card=
      (countingSourceColumn t (hexIndexEquiv i)).card := by
  have he : ((countingSourceOctadEquiv t).val ∩ tetrad i).image countingPointCoordinates=
      {hexIndexEquiv i} ×ˢ countingSourceColumn t (hexIndexEquiv i) := by
    ext z
    constructor
    · rintro hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      have hi := (mem_tetrad p i).mp (Finset.mem_inter.mp hp).2
      have hc := (countingSourceColumn_membership t p).mp (Finset.mem_inter.mp hp).1
      have hfirst : (countingPointCoordinates p).1=hexIndexEquiv i := congrArg hexIndexEquiv hi
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hfirst,by simpa only [hfirst] using hc⟩
    · intro hz
      obtain ⟨hzi,hzc⟩ := Finset.mem_product.mp hz
      have hzi := Finset.mem_singleton.mp hzi
      let p := countingPointCoordinates.symm z
      have hp : countingPointCoordinates p=z := Equiv.apply_symm_apply _ z
      refine Finset.mem_image.mpr ⟨p,Finset.mem_inter.mpr ⟨?_,?_⟩,hp⟩
      · apply (countingSourceColumn_membership t p).mpr
        rw [hp,hzi]
        exact hzc
      · apply (mem_tetrad p i).mpr
        apply hexIndexEquiv.injective
        exact (congrArg Prod.fst hp).trans hzi
  have hc := Finset.card_image_of_injective
    ((countingSourceOctadEquiv t).val ∩ tetrad i) countingPointCoordinates.injective
  rw [he,Finset.card_product,Finset.card_singleton,one_mul] at hc
  exact hc.symm

theorem cubicCommonNeighbor_two_column_card (G : Finset Omega) (i j : HexIndex) (hij : i ≠ j) :
    ((tetrad i ∪ tetrad j) ∩ G).card=(G ∩ tetrad i).card+(G ∩ tetrad j).card := by
  have hd : Disjoint (G ∩ tetrad i) (G ∩ tetrad j) := by
    apply Finset.disjoint_left.mpr
    intro p hi hj
    exact hij (((mem_tetrad p i).mp (Finset.mem_inter.mp hi).2).symm.trans
      ((mem_tetrad p j).mp (Finset.mem_inter.mp hj).2))
  rw [Finset.inter_comm,Finset.inter_union_distrib_left,Finset.card_union_of_disjoint hd]

theorem cubicCommonNeighbor_column_union_inter (i j k : HexIndex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tetrad i ∪ tetrad j) ∩ (tetrad i ∪ tetrad k)=tetrad i := by
  ext p
  simp only [Finset.mem_inter,Finset.mem_union,mem_tetrad]
  constructor
  · intro h
    obtain ⟨h1,h2⟩ := h
    rcases h1 with h | h
    · exact h
    · rcases h2 with h' | h'
      · exact h'
      · exact False.elim (hjk (h.symm.trans h'))
  · intro h
    exact ⟨Or.inl h,Or.inl h⟩

theorem cubicCommonNeighbor_source_card (D F : Octad) (i j k : HexIndex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hD : D.val=tetrad i ∪ tetrad j) (hF : F.val=tetrad i ∪ tetrad k) (u : ℕ) :
    Nat.card (CubicSourceCommonNeighbors (hexIndexEquiv i) (hexIndexEquiv j) (hexIndexEquiv k) u)=
      cubicCommonNeighborCount D F u := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv countingSourceOctadEquiv
  intro t
  change _ ↔ (D.val ∩ (countingSourceOctadEquiv t).val).card=4 ∧
    (F.val ∩ (countingSourceOctadEquiv t).val).card=4 ∧
    ((D.val ∩ F.val) ∩ (countingSourceOctadEquiv t).val).card=u
  rw [hD,hF,cubicCommonNeighbor_two_column_card _ i j hij,
    cubicCommonNeighbor_two_column_card _ i k hik,
    cubicCommonNeighbor_column_union_inter i j k hij hik hjk,Finset.inter_comm (tetrad i)]
  simp only [cubicCommonNeighbor_column_card]
  rfl

end Atlas.Fischer
