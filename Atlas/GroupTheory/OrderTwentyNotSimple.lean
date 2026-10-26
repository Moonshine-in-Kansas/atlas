import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic

/-! A group of order twenty has a unique proper nontrivial Sylow five subgroup. -/
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem not_simple_of_card_twenty (hG : Nat.card G=20) : ¬ IsSimpleGroup G := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := Classical.choice inferInstance
  have hd : Nat.card (Sylow 5 G) ∣ 20 := by
    rw [← hG]
    exact P.card_dvd_index.trans P.toSubgroup.index_dvd_card
  have hm := card_sylow_modEq_one 5 G
  have hc : Nat.card (Sylow 5 G)=1 := by
    have hle : Nat.card (Sylow 5 G)≤20 := Nat.le_of_dvd (by decide) hd
    have hmod : Nat.card (Sylow 5 G)%5=1 := hm
    interval_cases hn : Nat.card (Sylow 5 G) <;> norm_num at *
  letI : Subsingleton (Sylow 5 G) := Finite.card_le_one_iff_subsingleton.mp hc.le
  letI : P.toSubgroup.Normal := P.normal_of_subsingleton
  intro hs
  letI := hs
  rcases (inferInstance : P.toSubgroup.Normal).eq_bot_or_eq_top with hb | ht
  · exact P.ne_bot_of_dvd_card (by rw [hG]; decide) hb
  · have hp := P.card_coprime_index
    have hP : Nat.card P=5 := by
      rw [P.card_eq_multiplicity,hG]
      rw [show 20=5*4 by decide, Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 5 4),
        Nat.Prime.factorization_self (by decide : Nat.Prime 5),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5 ∣ 4)]
      norm_num
    have he : Nat.card P=Nat.card G := by
      change Nat.card (P : Subgroup G)=Nat.card G
      rw [ht]
      exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
    omega
end Atlas.GroupTheory
