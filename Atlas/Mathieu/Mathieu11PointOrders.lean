import Atlas.Mathieu.Mathieu11SharpAction

noncomputable section
namespace Atlas.Codes

def mathieu11OrderedStabilizer (D : Dodecad) (a : Mathieu12Points D) {k : ℕ}
    (e : Fin k ↪ Mathieu11Points D a) : Subgroup (Mathieu11PointModel D a) :=
  fixingSubgroup (Mathieu11PointModel D a) (Set.range e)

theorem mathieu11OrderedStabilizer_order_product (D : Dodecad) (a : Mathieu12Points D) {k : ℕ}
    (e : Fin k ↪ Mathieu11Points D a) (hk : k ≤ 4) :
    Nat.card (mathieu11OrderedStabilizer D a e) * ((11).choose k * k.factorial) = 7920 := by
  have := mathieu11_four_transitive D a
  have hn : (Set.range e).ncard = k := by
    rw [Set.ncard_range_of_injective e.injective]; simp
  have ht : MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a)
      (Mathieu11Points D a) (Set.range e).ncard := by
    rw [hn]
    apply MulAction.isMultiplyPretransitive_of_le hk
    rw [mathieu11_degree]; omega
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht
  have he := (mathieu11OrderedStabilizer D a e).card_mul_index
  rw [hn,mathieu11_degree] at hi
  change (mathieu11OrderedStabilizer D a e).index = Nat.choose 11 k * k.factorial at hi
  rw [hi,mathieu11_order] at he
  exact he

theorem mathieu11_one_point_order (D : Dodecad) (a : Mathieu12Points D) (e : Fin 1 ↪ Mathieu11Points D a) :
    Nat.card (mathieu11OrderedStabilizer D a e) = 720 := by
  have h := mathieu11OrderedStabilizer_order_product D a e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu11_two_point_order (D : Dodecad) (a : Mathieu12Points D) (e : Fin 2 ↪ Mathieu11Points D a) :
    Nat.card (mathieu11OrderedStabilizer D a e) = 72 := by
  have h := mathieu11OrderedStabilizer_order_product D a e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu11_three_point_order (D : Dodecad) (a : Mathieu12Points D) (e : Fin 3 ↪ Mathieu11Points D a) :
    Nat.card (mathieu11OrderedStabilizer D a e) = 8 := by
  have h := mathieu11OrderedStabilizer_order_product D a e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu11_four_point_order (D : Dodecad) (a : Mathieu12Points D) (e : Fin 4 ↪ Mathieu11Points D a) :
    Nat.card (mathieu11OrderedStabilizer D a e) = 1 := by
  have h := mathieu11OrderedStabilizer_order_product D a e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  simp [h]

theorem mathieu11_not_five_transitive (D : Dodecad) (a : Mathieu12Points D) :
    ¬ MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) 5 := by
  intro ht
  classical
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ Mathieu11Points D a) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin,← Nat.card_eq_fintype_card,mathieu11_degree]; omega)
  have hn : (Set.range e).ncard = 5 := by
    rw [Set.ncard_range_of_injective e.injective]; simp
  have ht' : MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a)
      (Mathieu11Points D a) (Set.range e).ncard := hn.symm ▸ ht
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht'
  have he := (fixingSubgroup (Mathieu11PointModel D a) (Set.range e)).card_mul_index
  rw [hi,hn,mathieu11_degree,mathieu11_order] at he
  norm_num [Nat.choose,Nat.factorial] at he
  omega

end Atlas.Codes
