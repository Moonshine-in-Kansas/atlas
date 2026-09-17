import Atlas.Fischer.MathieuOctadInsideAction
import Atlas.GroupTheory.SmallIndexSimple
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Data.Fintype.CardEmbedding

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadInterior_card (O : Octad) : Nat.card (OctadInterior O) = 8 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  exact octad_size O.val O.prop

theorem mathieuOctadInterior_five_transitive (O : Octad)
    (e f : Fin 5 ↪ OctadInterior O) :
    ∃ g : MathieuOctadStabilizer O, ∀ k, mathieuOctadInteriorPerm O g (e k) = f k := by
  classical
  let e' : Fin 5 ↪ Omega := e.trans (Function.Embedding.subtype _)
  let f' : Fin 5 ↪ Omega := f.trans (Function.Embedding.subtype _)
  obtain ⟨g,hg⟩ := mathieu24_five_transitive_explicit e' f'
  let F := Finset.univ.image f'
  have hF : F.card=5 := by
    rw [Finset.card_image_of_injective _ f'.injective]
    simp
  have hFO : F ⊆ O.val := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact (f k).prop
  have hFg : F ⊆ permuteBlock g.val O.val := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨e' k,(e k).prop,hg k⟩
  have hgo := octad_unique_on_five F _ O.val hF
    (codePreserving_octad_forward g.val g.prop O.val O.prop) O.prop hFg hFO
  refine ⟨⟨g,(mathieuOctadStabilizer_iff O g).mpr hgo⟩,?_⟩
  intro k
  exact Subtype.ext (hg k)

def octadFiveEmbedding (O : Octad) : Fin 5 ↪ OctadInterior O :=
  (Fin.castLEEmb (show 5 ≤ 8 by decide)).trans
    (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card,octadInterior_card])).symm.toEmbedding

theorem mathieuOctadInside_image_lower (O : Octad) :
    6720 ≤ Nat.card (mathieuOctadAlternatingHom O).range := by
  classical
  let e := octadFiveEmbedding O
  let f : (mathieuOctadAlternatingHom O).range → (Fin 5 ↪ OctadInterior O) :=
    fun h => e.trans h.val.val.toEmbedding
  have hs : Function.Surjective f := by
    intro t
    obtain ⟨g,hg⟩ := mathieuOctadInterior_five_transitive O e t
    refine ⟨⟨mathieuOctadAlternatingHom O g,⟨g,rfl⟩⟩,?_⟩
    apply Function.Embedding.ext
    exact hg
  have hc := Nat.card_le_card_of_surjective f hs
  have he : Nat.card (Fin 5 ↪ OctadInterior O)=6720 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq]
    rw [← Nat.card_eq_fintype_card,octadInterior_card]
    norm_num [Nat.descFactorial]
  rwa [he] at hc

theorem octadAlternating_card (O : Octad) : Nat.card (alternatingGroup (OctadInterior O))=20160 := by
  letI : Nontrivial (OctadInterior O) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [octadInterior_card]; decide)
  rw [nat_card_alternatingGroup,octadInterior_card]
  norm_num

theorem mathieuOctadAlternating_surjective (O : Octad) :
    Function.Surjective (mathieuOctadAlternatingHom O) := by
  letI : IsSimpleGroup (alternatingGroup (OctadInterior O)) :=
    alternatingGroup.isSimpleGroup (by rw [octadInterior_card]; decide)
  let H := (mathieuOctadAlternatingHom O).range
  have hc := H.card_mul_index
  rw [octadAlternating_card] at hc
  have hl := mathieuOctadInside_image_lower O
  change 6720 ≤ Nat.card H at hl
  have hi : H.index ≤ 3 := by
    by_contra hn
    have h := Nat.mul_le_mul hl (show 4 ≤ H.index by omega)
    rw [hc] at h
    norm_num at h
  have ht : H=⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt H (by
    rw [octadAlternating_card]
    interval_cases h : H.index <;> norm_num [h])
  exact MonoidHom.range_eq_top.mp ht

/-- The actual pointwise octad stabilizer, as the kernel of its restriction. -/
def mathieuOctadPointwise (O : Octad) : Subgroup (MathieuOctadStabilizer O) :=
  (mathieuOctadAlternatingHom O).ker

theorem mathieuOctadPointwise_order (O : Octad) : Nat.card (mathieuOctadPointwise O)=16 := by
  have he := (mathieuOctadPointwise O).card_mul_index
  have hi : (mathieuOctadPointwise O).index=20160 := by
    rw [mathieuOctadPointwise,Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (mathieuOctadAlternating_surjective O),Subgroup.card_top,
      octadAlternating_card]
  rw [hi,mathieuOctadStabilizer_order] at he
  omega

end Atlas.Fischer
