import Atlas.Mathieu.DodecadFiveFree
import Atlas.GroupTheory.FreeActionCard
import Mathlib.Data.Fintype.CardEmbedding

noncomputable section
namespace Atlas.Codes

 theorem mathieu12_five_tuple_free (D : Dodecad) (e : Fin 5 ↪ Mathieu12Points D)
    (g : Mathieu12DodecadModel D) (hg : g • e = e) : g = 1 := by
  apply Subtype.ext
  apply dodecad_five_fixed D (e.trans (Function.Embedding.subtype _))
    (fun k => (e k).prop) g.val ((mathieu12_mem D g.val).mp g.prop)
  intro k
  exact congrArg (fun f : Fin 5 ↪ Mathieu12Points D => (f k).val) hg

theorem mathieu12_sharp_five_transitive (D : Dodecad)
    (e f : Fin 5 ↪ Mathieu12Points D) : ∃! g : Mathieu12DodecadModel D, g • e = f := by
  apply Atlas.GroupTheory.unique_smul_of_free_card _ (mathieu12_five_tuple_free D) e f
  classical
  rw [mathieu12_order,Nat.card_eq_fintype_card,Fintype.card_embedding_eq,Fintype.card_fin,
    ← Nat.card_eq_fintype_card,mathieu12_degree]
  rfl

theorem mathieu12_five_transitive (D : Dodecad) :
    MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D) (Mathieu12Points D) 5 := by
  apply MulAction.isMultiplyPretransitive_iff.mpr
  intro e f
  exact (mathieu12_sharp_five_transitive D e f).exists

theorem mathieu12_faithful (D : Dodecad) : FaithfulSMul (Mathieu12DodecadModel D) (Mathieu12Points D) := by
  classical
  have hc : Fintype.card (Fin 5) ≤ Fintype.card (Mathieu12Points D) := by
    rw [Fintype.card_fin,← Nat.card_eq_fintype_card,mathieu12_degree]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  constructor
  intro g h he
  have hf : (h⁻¹*g) • e = e := by
    apply Function.Embedding.ext
    intro k
    change (h⁻¹*g) • e k = e k
    rw [mul_smul,he,inv_smul_smul]
  exact (inv_mul_eq_one.mp (mathieu12_five_tuple_free D e (h⁻¹*g) hf)).symm

end Atlas.Codes
