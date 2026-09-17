import Atlas.Fischer.OctadQuadraticIsometry
import Atlas.Algebra.BinaryQuadraticWordRank
import Atlas.Fischer.OctadRestrictionCounts

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators

theorem octadEvenRestriction_weight (O : Octad) (c : golay) :
    hammingNorm (octadEvenRestriction O c).val=(support c.val ∩ O.val).card := by
  classical
  rw [hammingNorm_eq_sum]
  change (∑ i : O.val, if c.val i.val=0 then 0 else 1)=_
  rw [Finset.sum_coe_sort O.val (fun i : Omega => if c.val i=0 then (0 : ℕ) else 1)]
  have he : support c.val ∩ O.val=O.val.filter (fun i => c.val i ≠ 0) := by
    ext i
    simp [support,and_comm]
  rw [he,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- Equality on the marked octad changes the punctured word only by an affine
function; hence the actual normalized polar maps coincide. -/
theorem octadQuadraticPolar_eq_of_restriction (O : Octad) (c d : golay)
    (h : octadEvenRestriction O c=octadEvenRestriction O d) :
    (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin=
      (binaryQuadraticWordForm (octadQuadraticRestriction O d)).polarBilin := by
  have hm : c-d ∈ octadShortenedCode O := by
    rw [← octadEvenRestriction_kernel]
    change octadEvenRestriction O (c-d)=0
    rw [map_sub,h,sub_self]
  have hw : octadExteriorWord O (c-d) ∈ binaryAffineCode := by
    rw [← octadExterior_map_shortened O]
    exact ⟨c-d,hm,rfl⟩
  have hneg : -(octadExteriorWord O d)=octadExteriorWord O d := by
    funext v
    exact CharTwo.neg_eq _
  rw [map_sub,sub_eq_add_neg,hneg] at hw
  exact binaryQuadraticWordForm_polar_eq_of_affine _ _ hw

theorem octadEvenRestriction_eq_of_support (O : Octad) (c d : golay)
    (h : support c.val ∩ O.val=support d.val ∩ O.val) :
    octadEvenRestriction O c=octadEvenRestriction O d := by
  apply Subtype.ext
  funext i
  change c.val i.val=d.val i.val
  have he := Finset.ext_iff.mp h i.val
  have hh : c.val i.val ≠ 0 ↔ d.val i.val ≠ 0 := by
    simpa [support,i.property] using he
  exact (show ∀ a b : Bit, (a ≠ 0 ↔ b ≠ 0) → a=b by decide) _ _ hh

theorem octadQuadraticWord_rank_duad_octad (O D : Octad) (h : (D.val ∩ O.val).card=2) :
    binaryWalshPolarRank (binaryQuadraticWordForm (octadQuadraticRestriction O (octadWord D)))=4 := by
  apply binaryQuadraticWordForm_rank_four_of_weight_six
  have hw := octadComplementary_restriction_weights O (octadWord D)
  rw [octadEvenRestriction_weight,octadWord_support,octadWord_weight,h] at hw
  change hammingNorm (octadExteriorWord O (octadWord D))=6
  omega

theorem octadQuadraticWord_rank_tetrad_octad (O D : Octad) (h : (D.val ∩ O.val).card=4) :
    binaryWalshPolarRank (binaryQuadraticWordForm (octadQuadraticRestriction O (octadWord D)))=2 := by
  apply binaryQuadraticWordForm_rank_two_of_weight_four
  have hw := octadComplementary_restriction_weights O (octadWord D)
  rw [octadEvenRestriction_weight,octadWord_support,octadWord_weight,h] at hw
  change hammingNorm (octadExteriorWord O (octadWord D))=4
  omega

theorem exists_octad_with_restriction (O : Octad) (S : Finset Omega)
    (hS : S ⊆ O.val) (hcard : S.card=2 ∨ S.card=4) :
    ∃ D : Octad, D.val ∩ O.val=S := by
  classical
  have hn : 0 < octadRestrictionCount O.val S := by
    rcases hcard with h | h
    · rw [octadRestrictionCount_duad O.val S O.property hS h]; decide
    · rw [octadRestrictionCount_tetrad O.val S O.property hS h]; decide
  obtain ⟨D,hD⟩ := Finset.card_pos.mp hn
  rcases Finset.mem_filter.mp hD with ⟨hd,he⟩
  exact ⟨⟨D,hd⟩,he⟩

/-- Every actual duad class has rank four, regardless of the Golay representative. -/
theorem octadQuadraticWord_rank_duad (O : Octad) (c : golay)
    (h : (support c.val ∩ O.val).card=2) :
    binaryWalshPolarRank (binaryQuadraticWordForm (octadQuadraticRestriction O c))=4 := by
  obtain ⟨D,hD⟩ := exists_octad_with_restriction O (support c.val ∩ O.val)
    Finset.inter_subset_right (Or.inl h)
  have he : octadEvenRestriction O c=octadEvenRestriction O (octadWord D) := by
    apply octadEvenRestriction_eq_of_support
    rw [octadWord_support,hD]
  unfold binaryWalshPolarRank
  rw [octadQuadraticPolar_eq_of_restriction O c (octadWord D) he]
  exact octadQuadraticWord_rank_duad_octad O D (by rw [hD,h])

/-- Every actual tetrad class has rank two, independently of its chosen lift. -/
theorem octadQuadraticWord_rank_tetrad (O : Octad) (c : golay)
    (h : (support c.val ∩ O.val).card=4) :
    binaryWalshPolarRank (binaryQuadraticWordForm (octadQuadraticRestriction O c))=2 := by
  obtain ⟨D,hD⟩ := exists_octad_with_restriction O (support c.val ∩ O.val)
    Finset.inter_subset_right (Or.inr h)
  have he : octadEvenRestriction O c=octadEvenRestriction O (octadWord D) := by
    apply octadEvenRestriction_eq_of_support
    rw [octadWord_support,hD]
  unfold binaryWalshPolarRank
  rw [octadQuadraticPolar_eq_of_restriction O c (octadWord D) he]
  exact octadQuadraticWord_rank_tetrad_octad O D (by rw [hD,h])

end Atlas.Fischer
