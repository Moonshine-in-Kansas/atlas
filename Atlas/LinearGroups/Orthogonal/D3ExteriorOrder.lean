import Atlas.LinearGroups.ProjectiveSpecialLinear
import Atlas.LinearGroups.Orthogonal.ProjectiveDOrderAllChar

/-! # Independent order comparison for the exterior-square A3/D3 map

Only the independently established uniform group-order formulas are used.
There is no dependency on the exterior-square comparison or on simplicity.
-/
noncomputable section
namespace Atlas.Orthogonal.D3Exterior
open scoped MatrixGroups

/-- The two projective scalar denominators coincide in rank three. -/
theorem gcd_four_cube_sub_one (q : ℕ) (hq : 1 ≤ q) :
    Nat.gcd 4 (q ^ 3 - 1) = Nat.gcd 4 (q - 1) := by
  have ho : Odd (q ^ 2 + q + 1) := by
    rw [Nat.odd_iff]
    rcases Nat.mod_two_eq_zero_or_one q with hm | hm <;>
      simp [Nat.add_mod,Nat.pow_mod,hm]
  have hc : Nat.Coprime (q ^ 2 + q + 1) 4 := ho.coprime_two_right.pow_right 2
  have he : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have h := Nat.sub_add_cancel hq
    have hp : (q - 1) * (q ^ 2 + q + 1) + 1 = q ^ 3 := by nlinarith
    omega
  rw [he]
  exact hc.gcd_mul_right_cancel_right (q - 1)

/-- Equality concerns the actual PSL4 and actual projective split-D3 carriers. -/
theorem card_psl_four_eq_projectiveD_three {F : Type*} [Field F] [Finite F] :
    Nat.card (PSL(4, F)) = Nat.card (ProjectiveElementary (formD 3 F)) := by
  rw [Atlas.card_psl_factor,card_projectiveD_all_char (F := F) 0]
  have hg := gcd_four_cube_sub_one (Nat.card F) (by have h := Finite.one_lt_card (α := F); omega)
  norm_num [Finset.prod_Icc_succ_top,Finset.prod_range_succ] at hg ⊢
  rw [hg]
  congr 1
  ring

end Atlas.Orthogonal.D3Exterior
