import Atlas.LinearGroups.Unitary.ProjectiveOrder
import Atlas.LinearGroups.Orthogonal.Minus.ProjectiveOrder

/-! Independent comparison of the already proved orders; no construction or recognition by order. -/
noncomputable section
namespace Atlas.Orthogonal.Minus

theorem gcd_four_cube_add_one (q : ℕ) : Nat.gcd 4 (q^3+1)=Nat.gcd 4 (q+1) := by
  have hq : q%4<4 := Nat.mod_lt _ (by decide)
  have h : q%4=0 ∨ q%4=1 ∨ q%4=2 ∨ q%4=3 := by omega
  rcases h with h | h | h | h <;>
    rw [Nat.gcd_rec,Nat.gcd_rec 4 (q+1)] <;>
    norm_num [Nat.add_mod,Nat.pow_mod,h]

variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankThree_projective_card_eq_unitary (hdeg : Module.finrank F K=2) :
    Nat.card (ProjectiveElementary (form hdeg 2))=Nat.card (Atlas.Unitary.PSU F K 4 hdeg) := by
  rw [card_projective hdeg 0,Atlas.Unitary.card_psu_factor hdeg 4 (by decide)]
  norm_num [Finset.prod_range_succ,Finset.prod_Icc_succ_top,
    Atlas.Unitary.orderFactor, Nat.even_iff]
  rw [gcd_four_cube_add_one]
  congr 1
  ring
end Atlas.Orthogonal.Minus
