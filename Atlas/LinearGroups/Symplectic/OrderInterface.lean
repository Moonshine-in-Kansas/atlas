import Atlas.LinearGroups.Symplectic.ProjectiveOrder

namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

theorem center_denominator_positive : 0 < Nat.gcd 2 (Nat.card F-1) :=
  Nat.gcd_pos_of_pos_left _ (by decide)

theorem center_mul_card_psp (hn : 0 < n) :
    Nat.gcd 2 (Nat.card F-1) * Nat.card (PSp n F) = orderNumerator n (Nat.card F) := by
  simpa only [mul_comm] using card_psp_mul_center (F := F) hn

end Atlas.Symplectic
