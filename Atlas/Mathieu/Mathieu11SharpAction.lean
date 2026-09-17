import Atlas.Mathieu.Mathieu11PointStabilizer

noncomputable section
namespace Atlas.Codes

theorem mathieu11_sharp_four_transitive (D : Dodecad) (a : Mathieu12Points D)
    (e f : Fin 4 ↪ Mathieu11Points D a) : ∃! g : Mathieu11PointModel D a, g • e = f := by
  have := mathieu11_four_transitive D a
  have hs : Function.Surjective (fun g : Mathieu11PointModel D a => g • e) :=
    fun f => MulAction.exists_smul_eq _ e f
  have hc : Nat.card (Mathieu11PointModel D a) = Nat.card (Fin 4 ↪ Mathieu11Points D a) := by
    classical
    rw [mathieu11_order,Nat.card_eq_fintype_card,Fintype.card_embedding_eq,Fintype.card_fin,
      ← Nat.card_eq_fintype_card,mathieu11_degree]
    rfl
  have hb := (Nat.bijective_iff_surjective_and_card (fun g : Mathieu11PointModel D a => g • e)).mpr ⟨hs,hc⟩
  obtain ⟨g,hg⟩ := hb.2 f
  exact ⟨g,hg,fun h hh => hb.1 (hh.trans hg.symm)⟩

theorem mathieu11_index (D : Dodecad) (a : Mathieu12Points D) : (Mathieu11PointModel D a).index = 12 := by
  have h := (Mathieu11PointModel D a).card_mul_index
  rw [mathieu11_order,mathieu12_order] at h
  omega

theorem mathieu11_order_product (D : Dodecad) (a : Mathieu12Points D) :
    12 * Nat.card (Mathieu11PointModel D a) = Nat.card (Mathieu12DodecadModel D) := by
  rw [mathieu11_order,mathieu12_order]

theorem mathieu11_order_from_sharp_action (D : Dodecad) (a : Mathieu12Points D)
    (e : Fin 4 ↪ Mathieu11Points D a) :
    Function.Bijective (fun g : Mathieu11PointModel D a => g • e) ∧
      Nat.card (Mathieu11PointModel D a) = 11*10*9*8 := by
  constructor
  · constructor
    · intro g h he
      obtain ⟨k,hk,hu⟩ := mathieu11_sharp_four_transitive D a e (g • e)
      exact (hu g rfl).trans (hu h he.symm).symm
    · intro f; exact (mathieu11_sharp_four_transitive D a e f).exists
  · rw [mathieu11_order]

end Atlas.Codes
