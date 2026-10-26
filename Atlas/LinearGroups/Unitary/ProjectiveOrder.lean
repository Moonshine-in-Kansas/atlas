import Atlas.LinearGroups.Unitary.Center
import Atlas.LinearGroups.Unitary.Order
import Mathlib.GroupTheory.Coset.Card

/-! # Independent order of the actual projective special unitary quotient

The denominator is obtained from the proved full center, rather than assumed
from a scalar candidate or inferred from a target finite group. -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Cardinality of the actual quotient times the actual full center. -/
theorem card_psu_mul_center (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (PSU F K n hdeg) * Nat.card (Subgroup.center (SU F K n hdeg)) =
      Nat.card (SU F K n hdeg) :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SU F K n hdeg))).symm

/-- Multiplied projective order, retaining the exact central divisor. -/
theorem card_psu_mul_gcd (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 0 < n) :
    Nat.card (PSU F K n hdeg) * Nat.gcd n (Nat.card F + 1) = orderSU (Nat.card F) n := by
  have h := card_psu_mul_center hdeg n
  rw [card_center hdeg hn, card_su hdeg n hn] at h
  exact h

/-- Exact divisibility is established before taking the natural-number quotient. -/
theorem center_factor_dvd_orderSU (hdeg : Module.finrank F K = 2)
    (n : ℕ) (hn : 0 < n) : Nat.gcd n (Nat.card F + 1) ∣ orderSU (Nat.card F) n := by
  refine ⟨Nat.card (PSU F K n hdeg), ?_⟩
  rw [← card_psu_mul_gcd hdeg n hn, Nat.mul_comm]

/-- Uniform projective special unitary order on the retained center quotient. -/
theorem card_psu (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 0 < n) :
    Nat.card (PSU F K n hdeg) = orderSU (Nat.card F) n / Nat.gcd n (Nat.card F + 1) := by
  rw [← card_psu_mul_gcd hdeg n hn]
  exact (Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ hn)).symm

/-- Conventional factorization, with dimension and base-field cardinality explicit. -/
theorem card_psu_factor (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 0 < n) :
    Nat.card (PSU F K n hdeg) =
      (Nat.card F ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, orderFactor (Nat.card F) i) /
          Nat.gcd n (Nat.card F + 1) := by
  rw [card_psu hdeg n hn, orderSU_formula_Icc]
end Atlas.Unitary
