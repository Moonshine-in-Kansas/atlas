import Atlas.LinearGroups.Symplectic.Order
import Atlas.LinearGroups.Symplectic.Center

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Division-free order identity for the actual central quotient, in positive rank. -/
theorem card_psp_mul_center (hn : 0 < n) :
    Nat.card (PSp n F) * Nat.gcd 2 (Nat.card F - 1) = orderNumerator n (Nat.card F) := by
  rw [← card_center hn, ← card_sp n F]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Sp n F))).symm

theorem center_order_dvd (hn : 0 < n) :
    Nat.gcd 2 (Nat.card F - 1) ∣ orderNumerator n (Nat.card F) :=
  ⟨Nat.card (PSp n F),by rw [← card_psp_mul_center hn, mul_comm]⟩

/-- Exact projective symplectic order over every finite field, including q=2 and q=3. -/
theorem card_psp (hn : 0 < n) : Nat.card (PSp n F) =
    orderNumerator n (Nat.card F) / Nat.gcd 2 (Nat.card F - 1) := by
  rw [← card_psp_mul_center hn, Nat.mul_div_cancel]
  exact Nat.gcd_pos_of_pos_left _ (by decide)

end Atlas.Symplectic
