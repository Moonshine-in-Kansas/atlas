import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Atlas.LinearGroups.PSLFamily
import Atlas.LinearGroups.ProjectiveSpecialLinear

namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups
local instance order168ModelsPrime1 : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem psl2Seven_card : Nat.card PSL(2, ZMod 7) = 168 := by
  rw [Atlas.card_psl_factor (F := ZMod 7) 2]
  norm_num [Nat.card_eq_fintype_card, Finset.prod_Icc_succ_top]

theorem psl3Two_card : Nat.card PSL(3, ZMod 2) = 168 := by
  rw [Atlas.card_psl_factor (F := ZMod 2) 3]
  norm_num [Nat.card_eq_fintype_card, Finset.prod_Icc_succ_top]

theorem sl3Two_center_eq_bot : Subgroup.center SL(3, ZMod 2) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Atlas.card_sl_center (ι := Fin 3) (F := ZMod 2)]
  norm_num [Nat.card_eq_fintype_card]

noncomputable def sl3TwoEquivPsl3Two : SL(3, ZMod 2) ≃* PSL(3, ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    apply (QuotientGroup.mk' _).ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk', sl3Two_center_eq_bot], QuotientGroup.mk'_surjective _⟩

theorem sl3Two_card : Nat.card SL(3, ZMod 2) = 168 := by
  rw [Nat.card_congr sl3TwoEquivPsl3Two.toEquiv, psl3Two_card]

theorem psl2Seven_simple : IsSimpleGroup PSL(2, ZMod 7) :=
  Atlas.psl_simple_rank_two (F := ZMod 7) (by norm_num [Nat.card_eq_fintype_card])

theorem psl3Two_simple : IsSimpleGroup PSL(3, ZMod 2) :=
  Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)

theorem sl3Two_simple : IsSimpleGroup SL(3, ZMod 2) := by
  letI := psl3Two_simple
  exact sl3TwoEquivPsl3Two.isSimpleGroup

end Atlas.Comparisons.Exceptional
