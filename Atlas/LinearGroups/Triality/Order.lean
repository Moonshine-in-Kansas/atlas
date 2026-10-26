import Atlas.LinearGroups.Triality.BruhatCard

/-! Uniform order of the actual generated triality matrix group. -/
noncomputable section
namespace Atlas.Triality
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem square_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (n-1)*(n+1)=n^2-1 := by
  have hh := Nat.sub_add_cancel hn
  have hp : (n-1)*(n+1)+1=n^2 := by nlinarith
  omega

/-- Order over an arbitrary cubic extension of finite fields, in every characteristic. -/
theorem card_group (hdeg : Module.finrank F K = 3) :
    Nat.card (Group F K) =
      Nat.card F^12 * (Nat.card F^8+Nat.card F^4+1) * (Nat.card F^6-1) * (Nat.card F^2-1) := by
  rw [card_group_bruhat_sum F K hdeg,weyl_weighted_sum,card_borel F K hdeg]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hq3 : 1 ≤ Nat.card F^3 := Nat.one_le_pow _ _ hq
  calc
    _ = Nat.card F^12 * (Nat.card F^8+Nat.card F^4+1) *
      ((Nat.card F^3-1)*(Nat.card F^3+1)) * ((Nat.card F-1)*(Nat.card F+1)) := by ring
    _ = _ := by rw [square_sub_one _ hq3,square_sub_one _ hq]; simp [← pow_mul]

end Atlas.Triality
