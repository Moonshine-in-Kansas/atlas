import Atlas.LinearGroups.Orthogonal.Minus.ProjectiveOrder

/-! Numerical specializations of the proved uniform order, not independent certificates. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem order_rank_three_binary (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2) :
    Nat.card (ProjectiveElementary (form hdeg 2)) = 25920 := by
  have h := card_projective hdeg 0
  norm_num [hq,Finset.prod_range_succ] at h
  exact h

theorem order_rank_three_ternary (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 3) :
    Nat.card (ProjectiveElementary (form hdeg 2)) = 3265920 := by
  have h := card_projective hdeg 0
  norm_num [hq,Finset.prod_range_succ] at h
  exact h

theorem order_rank_four_binary (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2) :
    Nat.card (ProjectiveElementary (form hdeg 3)) = 197406720 := by
  have h := card_projective hdeg 1
  norm_num [hq,Finset.prod_range_succ] at h
  exact h

theorem order_rank_four_ternary (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 3) :
    Nat.card (ProjectiveElementary (form hdeg 3)) = 10151968619520 := by
  have h := card_projective hdeg 1
  norm_num [hq,Finset.prod_range_succ] at h
  exact h

theorem center_rank_three_ternary (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F) ≠ 0) (hq : Nat.card F = 3) :
    Nat.card (Subgroup.center (E hdeg 2)) = 2 := by
  convert card_elementary_center_mod_four hdeg 0 h2 using 1 <;> norm_num [hq]

theorem center_rank_four_ternary (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F) ≠ 0) (hq : Nat.card F = 3) :
    Nat.card (Subgroup.center (E hdeg 3)) = 1 := by
  convert card_elementary_center_mod_four hdeg 1 h2 using 1 <;> norm_num [hq]
end Atlas.Orthogonal.Minus
