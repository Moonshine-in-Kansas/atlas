import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Data.Finset.Card

noncomputable section
namespace Atlas.Combinatorics
open Finset
attribute [local instance] Classical.propDecidable

/-- Multiple transitivity acts transitively on subsets of the same permitted size. -/
theorem multiply_transitive_finset_image {G V : Type*} [Group G] [MulAction G V] [DecidableEq V]
    {k : ℕ} [MulAction.IsMultiplyPretransitive G V k]
    (S T : Finset V) (hS : S.card = k) (hT : T.card = k) :
    ∃ g : G, S.image (fun v => g • v) = T := by
  classical
  let eS : Fin k ≃ S := Fintype.equivOfCardEq (by simp [hS])
  let eT : Fin k ≃ T := Fintype.equivOfCardEq (by simp [hT])
  let fS := eS.toEmbedding.trans (Function.Embedding.subtype _)
  let fT := eT.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G fS fT
  have hm (i : Fin k) : g • (eS i).val = (eT i).val := congrArg (fun e : Fin k ↪ V => e i) hg
  refine ⟨g,?_⟩
  ext v
  constructor
  · rintro hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    obtain ⟨i,hi⟩ := eS.surjective ⟨u,hu⟩
    have he : (eS i).val = u := congrArg Subtype.val hi
    rw [← he,hm]
    exact (eT i).prop
  · intro hv
    obtain ⟨i,hi⟩ := eT.surjective ⟨v,hv⟩
    exact mem_image.mpr ⟨(eS i).val,(eS i).prop,(hm i).trans (congrArg Subtype.val hi)⟩

/-- Uniqueness of the block through a t-subset turns t-transitivity into block transitivity. -/
theorem steiner_block_transitive {G V : Type*} [Group G] [MulAction G V] [DecidableEq V]
    {t k : ℕ} [MulAction.IsMultiplyPretransitive G V t]
    (blocks : Finset (Finset V)) (htk : t ≤ k)
    (hsize : ∀ B ∈ blocks, B.card = k)
    (hunique : ∀ T : Finset V, T.card = t → ∃! B, B ∈ blocks ∧ T ⊆ B)
    (hpres : ∀ g : G, ∀ B ∈ blocks, B.image (fun v => g • v) ∈ blocks)
    (B C : Finset V) (hB : B ∈ blocks) (hC : C ∈ blocks) :
    ∃ g : G, B.image (fun v => g • v) = C := by
  classical
  obtain ⟨S,hSB,hS⟩ := exists_subset_card_eq (s := B) (n := t) (by rw [hsize B hB]; exact htk)
  obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (s := C) (n := t) (by rw [hsize C hC]; exact htk)
  obtain ⟨g,hg⟩ := multiply_transitive_finset_image (G := G) S T hS hT
  obtain ⟨D,_,hD⟩ := hunique T hT
  refine ⟨g,(hD _ ⟨hpres g B hB,?_⟩).trans (hD C ⟨hC,hTC⟩).symm⟩
  rw [← hg]
  exact image_subset_image hSB

end Atlas.Combinatorics
