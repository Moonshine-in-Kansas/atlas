import Atlas.LinearGroups.Orthogonal.Minus.RankTwoComparison

/-! Rank-two order in the same normalization as the uniform minus-family formula. -/
namespace Atlas.Orthogonal.Minus

private theorem rankTwo_gcd (q : ℕ) (hq : 2 ≤ q) :
    Nat.gcd 2 (q^2-1) = Nat.gcd 4 (q^2+1) := by
  have hs : 1 ≤ q^2 := by nlinarith
  have hbound := Nat.mod_lt q (by decide : 0 < 4)
  interval_cases h : q % 4 <;>
    have hm : q^2 % 4 = (q%4)*(q%4)%4 := by simp [pow_two,Nat.mul_mod]
  all_goals simp only [h] at hm
  all_goals norm_num at hm
  all_goals rw [Nat.gcd_rec 2, Nat.gcd_rec 4]
  all_goals have ha : (q^2-1)%2 = (if q^2%4=0 then 1 else 0) := by norm_num [hm]; omega
  all_goals have hb : (q^2+1)%4 = (if q^2%4=0 then 1 else 2) := by norm_num [hm]; omega
  all_goals rw [ha,hb]; norm_num [hm]

theorem rankTwo_projective_order_uniform {F K : Type*} [Field F] [Field K]
    [Finite F] [Finite K] [Algebra F K] (hdeg : Module.finrank F K = 2) :
    Nat.card (ProjectiveElementary (form hdeg 1)) =
      (Nat.card F ^ 2 * (Nat.card F ^ 2+1) * (Nat.card F ^ 2-1)) /
        Nat.gcd 4 (Nat.card F ^ 2+1) := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hs : 1 ≤ Nat.card F ^ 2 := by nlinarith
  have hf : (Nat.card F ^ 2)^2-1 = (Nat.card F ^ 2+1)*(Nat.card F ^ 2-1) := by
    have hsub := Nat.sub_add_cancel hs
    have hsub2 := Nat.sub_add_cancel (one_le_pow₀ hs : 1 ≤ (Nat.card F ^ 2)^2)
    nlinarith
  rw [rankTwo_projective_order,rankTwo_gcd _ hq,hf,mul_assoc]

theorem rankTwo_order_binary {F K : Type*} [Field F] [Field K]
    [Finite F] [Finite K] [Algebra F K] (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F=2) : Nat.card (ProjectiveElementary (form hdeg 1))=60 := by
  rw [rankTwo_projective_order_uniform,hq]
  norm_num

theorem rankTwo_order_ternary {F K : Type*} [Field F] [Field K]
    [Finite F] [Finite K] [Algebra F K] (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F=3) : Nat.card (ProjectiveElementary (form hdeg 1))=360 := by
  rw [rankTwo_projective_order_uniform,hq]
  norm_num

end Atlas.Orthogonal.Minus
