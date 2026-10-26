import Atlas.GroupTheory.SmallIndexSimple
import Mathlib.GroupTheory.Sylow

/-! Small-order obstructions from genuine Sylow subgroups and the faithful
coset-action bound. No identification of a group from its order is used. -/
noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem not_simple_of_card_six (hG : Nat.card G = 6) : ¬ IsSimpleGroup G := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hP : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hG]
    decide +kernel
  have hi : P.toSubgroup.index = 2 := by
    have h := P.toSubgroup.card_mul_index
    change Nat.card P * P.toSubgroup.index = Nat.card G at h
    rw [hP, hG] at h
    omega
  intro hs
  letI := hs
  have ht : P.toSubgroup = ⊤ :=
    subgroup_eq_top_of_index_factorial_lt P.toSubgroup (by rw [hi, hG]; decide)
  have he : Nat.card P = Nat.card G := by
    change Nat.card P.toSubgroup = Nat.card G
    rw [ht]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
  omega

theorem not_simple_of_card_twelve (hG : Nat.card G = 12) : ¬ IsSimpleGroup G := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.choice inferInstance
  have hP : Nat.card P = 4 := by
    rw [Sylow.card_eq_multiplicity, hG]
    decide +kernel
  have hi : P.toSubgroup.index = 3 := by
    have h := P.toSubgroup.card_mul_index
    change Nat.card P * P.toSubgroup.index = Nat.card G at h
    rw [hP, hG] at h
    omega
  intro hs
  letI := hs
  have ht : P.toSubgroup = ⊤ :=
    subgroup_eq_top_of_index_factorial_lt P.toSubgroup (by rw [hi, hG]; decide)
  have he : Nat.card P = Nat.card G := by
    change Nat.card P.toSubgroup = Nat.card G
    rw [ht]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
  omega

end Atlas.GroupTheory
