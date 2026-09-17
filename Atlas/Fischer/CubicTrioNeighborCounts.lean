import Atlas.Fischer.CubicMixedNeighborCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

 theorem cubicTrioCompletion_complement (D F : Octad) (hDF : (D.val ∩ F.val).card = 0) :
    (cubicTrioCompletion D F hDF).val = (D.val ∪ F.val)ᶜ := by
  ext i
  have h := congrArg (fun c : golay => c.val i) (cubicTrioCompletion_word D F hDF)
  simp only [Submodule.coe_add,Pi.add_apply,octadWord_apply,golayOne,allOnes] at h
  have hn : ¬(i ∈ D.val ∧ i ∈ F.val) := by
    intro hi
    have hp := Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr hi⟩
    rw [hDF] at hp
    omega
  by_cases hd : i ∈ D.val <;> by_cases hf : i ∈ F.val <;>
    by_cases ht : i ∈ (cubicTrioCompletion D F hDF).val <;>
    simp [hd,hf,ht,show (2 : Bit) = 0 from rfl] at h hn ⊢

theorem cubicTrioCompletion_intersections (D F : Octad) (hDF : (D.val ∩ F.val).card = 0) :
    (D.val ∩ (cubicTrioCompletion D F hDF).val).card = 0 ∧
      (F.val ∩ (cubicTrioCompletion D F hDF).val).card = 0 := by
  rw [cubicTrioCompletion_complement]
  constructor <;> apply Finset.card_eq_zero.mpr <;> ext i <;> simp <;> tauto

theorem cubicTrioCompletion_intersection_sum (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 0) :
    (D.val ∩ G.val).card + (F.val ∩ G.val).card +
      ((cubicTrioCompletion D F hDF).val ∩ G.val).card = 8 := by
  have hd : Disjoint D.val F.val := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hDF)
  have hdg : Disjoint (D.val ∩ G.val) (F.val ∩ G.val) := hd.mono Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.card_union_of_disjoint hdg,← Finset.union_inter_distrib_right,
    cubicTrioCompletion_complement]
  have hc := Finset.card_inter_add_card_sdiff G.val (D.val ∪ F.val)
  have he : (D.val ∪ F.val)ᶜ ∩ G.val = G.val \ (D.val ∪ F.val) := by ext i; simp; tauto
  rw [he,Finset.inter_comm]
  exact hc.trans (octad_size G.val G.property)

theorem cubicPairIntersection_disjoint_bothFour (D F : Octad)
    (hDF : (D.val ∩ F.val).card = 0) :
    Nat.card (CubicPairIntersectionFibre D F 4 4) = 28 := by
  let T := cubicTrioCompletion D F hDF
  have hTD : (T.val ∩ D.val).card = 0 := by
    rw [Finset.inter_comm]
    exact (cubicTrioCompletion_intersections D F hDF).1
  have e : CubicPairIntersectionFibre D F 4 4 ≃ CubicPairIntersectionFibre T D 0 4 :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro G
      have hs := cubicTrioCompletion_intersection_sum D F G hDF
      change _ ↔ (T.val ∩ G.val).card = 0 ∧ (D.val ∩ G.val).card = 4
      change _ + _ + (T.val ∩ G.val).card = 8 at hs
      omega)
  rw [Nat.card_congr e]
  exact cubicCommonNeighbor_disjoint_pair_twentyEight T D hTD

theorem cubicPairIntersection_disjoint_bothZero (D F : Octad)
    (hDF : (D.val ∩ F.val).card = 0) :
    Nat.card (CubicPairIntersectionFibre D F 0 0) = 1 := by
  let T := cubicTrioCompletion D F hDF
  have ht := cubicTrioCompletion_intersections D F hDF
  let v : CubicPairIntersectionFibre D F 0 0 := ⟨T,ht⟩
  have hu (G : CubicPairIntersectionFibre D F 0 0) : G = v := by
    apply Subtype.ext
    apply Subtype.ext
    have hsub : G.val.val ⊆ T.val := by
      intro i hi
      rw [cubicTrioCompletion_complement]
      simp only [Finset.mem_compl,Finset.mem_union,not_or]
      constructor <;> intro h
      · have hp := Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr ⟨h,hi⟩⟩
        rw [G.property.1] at hp
        omega
      · have hp := Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr ⟨h,hi⟩⟩
        rw [G.property.2] at hp
        omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [octad_size T.val T.property,octad_size G.val.val G.val.property])
  letI : Unique (CubicPairIntersectionFibre D F 0 0) := ⟨⟨v⟩,hu⟩
  exact Nat.card_unique

/-- The two disjoint orientations of exactly one empty intersection. -/
abbrev CubicPairOneEmptyFibre (D F : Octad) :=
  CubicPairIntersectionFibre D F 0 4 ⊕ CubicPairIntersectionFibre D F 4 0

theorem cubicPairOneEmpty_four_card (D F : Octad)
    (hDF : (D.val ∩ F.val).card = 4) :
    Nat.card (CubicPairOneEmptyFibre D F) = 6 := by
  rw [Nat.card_sum,(cubicPairIntersection_four_mixed D F hDF).1,
    Nat.card_congr (cubicPairIntersectionSwap D F 4 0)]
  rw [(cubicPairIntersection_four_mixed F D (by simpa [Finset.inter_comm] using hDF)).1]

theorem cubicPairOneEmpty_zero_card (D F : Octad)
    (hDF : (D.val ∩ F.val).card = 0) :
    Nat.card (CubicPairOneEmptyFibre D F) = 56 := by
  rw [Nat.card_sum,cubicCommonNeighbor_disjoint_pair_twentyEight D F hDF,
    Nat.card_congr (cubicPairIntersectionSwap D F 4 0)]
  rw [cubicCommonNeighbor_disjoint_pair_twentyEight F D (by simpa [Finset.inter_comm] using hDF)]

end Atlas.Fischer

