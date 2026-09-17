import Atlas.Fischer.CubicQuadrilateralRowValues

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicQuadrilateral_oneEmpty_indicator (D : Octad) :
    (∑ F : Octad,∑ G : Octad,if CubicQuadrilateralRow D F G 5 then (1 : Scalar) else 0) = 3360 := by
  have hp (a b c : ℕ) :
      (if ((a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0)) ∧ (c = 4 ∨ c = 0) then (1 : Scalar) else 0) =
      (if a = 0 ∧ b = 4 ∧ c = 4 then 1 else 0) +
      (if a = 0 ∧ b = 4 ∧ c = 0 then 1 else 0) +
      (if a = 4 ∧ b = 0 ∧ c = 4 then 1 else 0) +
      (if a = 4 ∧ b = 0 ∧ c = 0 then 1 else 0) := by
    split_ifs <;> norm_num <;> omega
  have hp' (F G : Octad) :
      (if CubicQuadrilateralRow D F G 5 then (1 : Scalar) else 0) =
      (if (D.val ∩ F.val).card = 0 ∧ (D.val ∩ G.val).card = 4 ∧ (F.val ∩ G.val).card = 4 then 1 else 0) +
      (if (D.val ∩ F.val).card = 0 ∧ (D.val ∩ G.val).card = 4 ∧ (F.val ∩ G.val).card = 0 then 1 else 0) +
      (if (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 0 ∧ (F.val ∩ G.val).card = 4 then 1 else 0) +
      (if (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 0 ∧ (F.val ∩ G.val).card = 0 then 1 else 0) := by
    convert hp (D.val ∩ F.val).card (D.val ∩ G.val).card (F.val ∩ G.val).card using 1 <;>
      split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  simp_rw [hp',Finset.sum_add_distrib]
  rw [cubicQuadrilateral_indicator,cubicQuadrilateral_indicator,
    cubicQuadrilateral_indicator,cubicQuadrilateral_indicator]
  have he : (Nat.card (CubicQuadrilateralOneEmptyFibre D) : Scalar) =
      (Nat.card (CubicQuadrilateralFibre D 0 4 4) : Scalar) +
      (Nat.card (CubicQuadrilateralFibre D 0 4 0) : Scalar) +
      (Nat.card (CubicQuadrilateralFibre D 4 0 4) : Scalar) +
      (Nat.card (CubicQuadrilateralFibre D 4 0 0) : Scalar) := by
    rw [Nat.card_sum,Nat.card_sum,Nat.card_sum]
    push_cast
    ring
  rw [← he,(cubicQuadrilateral_remaining_distribution D).2.1]
  norm_num

theorem cubicQuadrilateralRow_count (D : Octad) (n : Fin 8) :
    (∑ F : Octad,∑ G : Octad,if CubicQuadrilateralRow D F G n then (1 : Scalar) else 0) =
      (cubicQuadrilateralRowCard n : Scalar) := by
  fin_cases n
  · have he := cubicQuadrilateral_refined_indicator D 0
    rw [(cubicQuadrilateral_refined_distribution D).1] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  · have he := cubicQuadrilateral_refined_indicator D 2
    rw [(cubicQuadrilateral_refined_distribution D).2.1] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  · have he := cubicQuadrilateral_refined_indicator D 3
    rw [(cubicQuadrilateral_refined_distribution D).2.2.1] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  · have he := cubicQuadrilateral_refined_indicator D 4
    rw [(cubicQuadrilateral_refined_distribution D).2.2.2] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  · have he := cubicQuadrilateral_indicator D 4 4 0
    rw [(cubicQuadrilateral_remaining_distribution D).1] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  · exact cubicQuadrilateral_oneEmpty_indicator D
  · have he := cubicQuadrilateral_indicator D 0 0 4
    rw [(cubicQuadrilateral_remaining_distribution D).2.2.1] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto
  · have he := cubicQuadrilateral_indicator D 0 0 0
    rw [(cubicQuadrilateral_remaining_distribution D).2.2.2] at he
    convert he using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> dsimp [CubicQuadrilateralRow] at * <;> first | rfl | tauto

theorem cubicQuadrilateralRow_weighted_count (D : Octad) (v : Fin 8 → Scalar) :
    (∑ F : Octad,∑ G : Octad,∑ n,
      if CubicQuadrilateralRow D F G n then v n else 0) =
      ∑ n,(cubicQuadrilateralRowCard n : Scalar) * v n := by
  have ht (F G : Octad) (n : Fin 8) :
      (if CubicQuadrilateralRow D F G n then v n else 0) =
      (if CubicQuadrilateralRow D F G n then (1 : Scalar) else 0) * v n := by
    split_ifs <;> simp
  simp_rw [ht]
  calc
    _ = ∑ F : Octad,∑ n : Fin 8,∑ G : Octad,
        (if CubicQuadrilateralRow D F G n then (1 : Scalar) else 0) * v n := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.sum_comm]
    _ = ∑ n : Fin 8,∑ F : Octad,∑ G : Octad,
        (if CubicQuadrilateralRow D F G n then (1 : Scalar) else 0) * v n := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      simp_rw [← Finset.sum_mul]
      rw [cubicQuadrilateralRow_count]

end Atlas.Fischer
