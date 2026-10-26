import Atlas.LinearGroups.Orthogonal.Minus.FullOrder
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB

/-! Orders from the intrinsic kernel indices, independently of simplicity. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem card_elementary_mul_four (hdeg : Module.finrank F K = 2) (n : ℕ)
    (h2 : (2 : F) ≠ 0) : Nat.card (E hdeg (n+2)) * 4 = Nat.card (O hdeg (n+2)) := by
  rw [← elementary_index_odd hdeg n h2,Subgroup.card_mul_index]

theorem card_elementary_mul_two [CharP F 2] (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (E hdeg (n+2)) * 2 = Nat.card (O hdeg (n+2)) := by
  simpa only [elementary_index_even hdeg n] using (E hdeg (n+2)).card_mul_index

theorem card_elementary_even [CharP F 2] (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (E hdeg (n+2)) =
      Nat.card F ^ ((n+3)*(n+2)) * (Nat.card F ^ (n+3)+1) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1) := by
  have h := card_elementary_mul_two hdeg n
  rw [card_full] at h
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  calc
    Nat.card (E hdeg (n+2)) * 2 = _ := h
    _ = _ := by ring

theorem card_projective_even [CharP F 2] (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (ProjectiveElementary (form hdeg (n+2))) =
      Nat.card F ^ ((n+3)*(n+2)) * (Nat.card F ^ (n+3)+1) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1) := by
  rw [Nat.card_congr (evenProjectiveElementaryEquiv _).toEquiv,card_elementary_even]
end Atlas.Orthogonal.Minus
