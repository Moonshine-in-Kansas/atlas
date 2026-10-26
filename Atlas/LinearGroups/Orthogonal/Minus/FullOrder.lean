import Atlas.LinearGroups.Orthogonal.Minus.OrderBase
import Atlas.LinearGroups.Orthogonal.Minus.OrderRecurrence

/-! Uniform full orthogonal order from norm-plane classification and actual pair stabilizers. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem difference_square (a : ℕ) (ha : 1 ≤ a) : (a+1)*(a-1) = a^2-1 := by
  have h : a-1+1 = a := Nat.sub_add_cancel ha
  have he : a^2 = (a+1)*(a-1)+1 := by nlinarith
  omega

/-- Half-dimension is k+1; valid even for the anisotropic plane k=0. -/
theorem card_full (hdeg : Module.finrank F K = 2) (k : ℕ) :
    Nat.card (O hdeg k) =
      2 * Nat.card F ^ ((k+1)*k) * (Nat.card F ^ (k+1)+1) *
        ∏ i ∈ Finset.range k, (Nat.card F ^ (2*(i+1))-1) := by
  induction k with
  | zero => simp [card_full_zero]
  | succ k ih =>
    rw [card_full_succ,ih,Finset.prod_range_succ]
    have hp : 1 ≤ Nat.card F ^ (k+1) := one_le_pow₀ Nat.card_pos
    have hd : (Nat.card F ^ (k+1)+1)*(Nat.card F ^ (k+1)-1) =
        Nat.card F ^ (2*(k+1))-1 := by
      rw [difference_square _ hp,← pow_mul]
      congr 2
      omega
    have hn : (k+1+1)*(k+1) = 2*(k+1)+(k+1)*k := by ring
    rw [hn,pow_add (Nat.card F) (2*(k+1)) ((k+1)*k)]
    calc
      _ = 2 * (Nat.card F ^ (2*(k+1)) * Nat.card F ^ ((k+1)*k)) *
          (Nat.card F ^ (k+1+1)+1) *
          ((∏ i ∈ Finset.range k, (Nat.card F ^ (2*(i+1))-1)) *
            ((Nat.card F ^ (k+1)+1)*(Nat.card F ^ (k+1)-1))) := by ring
      _ = _ := by rw [hd]
end Atlas.Orthogonal.Minus
