import Atlas.LinearGroups.ProjectiveSpecialLinear
import Mathlib.Tactic.Linarith

namespace Atlas
variable {F : Type*} [Field F] [Finite F]
open scoped MatrixGroups

theorem card_sl_two : Nat.card SL(2,F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card (α := F)
  have hz := (Subgroup.center SL(2,F)).card_eq_card_quotient_mul_card_subgroup
  change Nat.card SL(2,F) = Nat.card PSL(2,F) * Nat.card (Subgroup.center SL(2,F)) at hz
  rw [card_sl_center] at hz
  have hp := card_psl_mul_factors (F := F) 2
  simp only [Fintype.card_fin,Fin.prod_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one] at hp hz
  have he : Nat.card SL(2,F) * (q-1) = (q^2-1)*(q^2-q) := by
    rw [hz]
    simpa [q,mul_comm,mul_left_comm,mul_assoc] using hp
  have hqq : q ≤ q^2 := by nlinarith
  have hq2 : 1 ≤ q^2 := by omega
  have hsub := Nat.sub_add_cancel (show 1 ≤ q by omega)
  have hsub2 := Nat.sub_add_cancel hqq
  have hsub3 := Nat.sub_add_cancel hq2
  change Nat.card SL(2,F) = q * (q^2-1)
  have hr : (q^2-q) = q*(q-1) := by nlinarith
  rw [hr] at he
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
  simpa [mul_assoc,mul_comm,mul_left_comm] using he
end Atlas
