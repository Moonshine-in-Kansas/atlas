import Atlas.LinearGroups.Orthogonal.BInvolutionClasses
import Atlas.LinearGroups.Symplectic.ProjectiveInvolutionCount
import Atlas.Comparisons.Classical.OrthogonalOrder

/-! # The involution-class discriminator for same-order odd-characteristic B and C

The counts concern the actual public quadratic and symplectic quotient models.
Neither count is inferred from a classification table or group order.
-/
namespace Atlas.Comparisons.Classical
open Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

/-- The two actual class counts, including the low-rank equalities. -/
theorem oddB_C_involution_counts (n : ℕ) (hn : 1 ≤ n) (h2 : (2 : F) ≠ 0) :
    Atlas.k2 (B n F) = n ∧ Atlas.k2 (Atlas.Symplectic.PSp n F) = n/2+1 :=
  ⟨B_k2 n hn h2,Atlas.Symplectic.k2_psp (by omega) h2⟩

/-- From rank three onward the two odd-characteristic families are not isomorphic,
because an isomorphism preserves the number of involution conjugacy classes. -/
theorem oddB_not_equiv_C (n : ℕ) (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0) :
    ¬ Nonempty (B n F ≃* Atlas.Symplectic.PSp n F) := by
  apply Atlas.not_nonempty_mulEquiv_of_k2_ne
  rw [B_k2 n (by omega) h2,Atlas.Symplectic.k2_psp (by omega) h2]
  omega

/-- The exact same-order/nonisomorphism statement for the two public families. -/
theorem oddB_same_order_nonisomorphic_C (n : ℕ) (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0) :
    Nat.card (B n F) = Nat.card (Atlas.Symplectic.PSp n F) ∧
      ¬ Nonempty (B n F ≃* Atlas.Symplectic.PSp n F) :=
  ⟨oddB_card_eq_C n (by omega) h2,oddB_not_equiv_C n hn h2⟩
end Atlas.Comparisons.Classical
