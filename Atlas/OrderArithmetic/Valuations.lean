import Atlas.OrderArithmetic.Denominators
import Atlas.OrderArithmetic.ValuationCore
import Mathlib.Algebra.BigOperators.Associated

namespace Atlas.OrderArithmetic
open scoped BigOperators

private theorem not_dvd_minus_product {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (hpq : p ∣ q) (s : Finset ℕ) (e : ℕ → ℕ) (he : ∀ i ∈ s, 1 ≤ e i) :
    ¬ p ∣ ∏ i ∈ s, (q ^ e i - 1) :=
  hp.prime.not_dvd_finsetProd fun i hi => prime_not_dvd_pow_sub_one hp hq hpq (he i hi)

/-- Every residual factor is prime to the characteristic. -/
theorem characteristic_not_dvd_residual {x : RawEntry} (hx : Admissible x)
    (hl : IsLie x) {p : ℕ} (hp : p.Prime) (hpq : p ∣ fieldSize x) : ¬ p ∣ residual x := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  cases x with
  | cyclic _ | alternating _ | fixed _ => exact hp.not_dvd_one
  | linear d q =>
    exact not_dvd_minus_product hp hq hpq _ _ (fun i hi => by
      have := (Finset.mem_Icc.mp hi).1; omega)
  | unitary d q =>
    apply hp.prime.not_dvd_finsetProd
    intro i hi
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.mp hi).1; omega
    unfold unitaryFactor
    split
    · exact prime_not_dvd_pow_sub_one hp hq hpq hi1
    · exact prime_not_dvd_pow_add_one hp hpq hi1
  | B r q | C r q =>
    exact not_dvd_minus_product hp hq hpq _ _ (fun i hi => by
      have := (Finset.mem_Icc.mp hi).1; omega)
  | Dplus r q =>
    apply hp.prime.not_dvd_mul
    · exact prime_not_dvd_pow_sub_one hp hq hpq (by have := hx.1; omega)
    · exact not_dvd_minus_product hp hq hpq _ _ (fun i hi => by
        have := (Finset.mem_Icc.mp hi).1; omega)
  | Dminus r q =>
    apply hp.prime.not_dvd_mul
    · exact prime_not_dvd_pow_add_one hp hpq (by have := hx.1; omega)
    · exact not_dvd_minus_product hp hq hpq _ _ (fun i hi => by
        have := (Finset.mem_Icc.mp hi).1; omega)
  | F4 q | E6 q | E7 q | E8 q =>
    apply not_dvd_minus_product hp hq hpq
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  | G2 q =>
    exact hp.prime.not_dvd_mul (prime_not_dvd_pow_sub_one hp hq hpq (by omega))
      (prime_not_dvd_pow_sub_one hp hq hpq (by omega))
  | twistedE6 q =>
    repeat apply hp.prime.not_dvd_mul
    all_goals first
      | exact prime_not_dvd_pow_sub_one hp hq hpq (by omega)
      | exact prime_not_dvd_pow_add_one hp hpq (by omega)
  | trialityD4 q =>
    apply hp.prime.not_dvd_mul
    · apply hp.prime.not_dvd_mul
      · intro h
        have h8 : p ∣ q ^ 8 := hpq.trans (dvd_pow_self _ (by omega))
        have h4 : p ∣ q ^ 4 := hpq.trans (dvd_pow_self _ (by omega))
        have hsub := Nat.dvd_sub h (dvd_add h8 h4)
        exact hp.not_dvd_one (by simpa using hsub)
      · exact prime_not_dvd_pow_sub_one hp hq hpq (by omega)
    · exact prime_not_dvd_pow_sub_one hp hq hpq (by omega)
  | suzuki q | smallRee q =>
    exact hp.prime.not_dvd_mul (prime_not_dvd_pow_add_one hp hpq (by omega))
      (by simpa [fieldSize] using prime_not_dvd_pow_sub_one hp hq hpq (show 1 ≤ 1 by omega))
  | largeRee q =>
    repeat apply hp.prime.not_dvd_mul
    all_goals first
      | exact prime_not_dvd_pow_sub_one hp hq hpq (by omega)
      | exact prime_not_dvd_pow_add_one hp hpq (by omega)
      | simpa [fieldSize] using prime_not_dvd_pow_sub_one hp hq hpq (show 1 ≤ 1 by omega)

theorem lie_order_eq {x : RawEntry} (hl : IsLie x) :
    order x = numerator x / denominator x := by
  cases x <;> simp_all [IsLie, order]

/-- Exact characteristic valuation for every admissible ordinary formula. -/
theorem order_characteristic_valuation {x : RawEntry} (hx : Admissible x) (hl : IsLie x)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : fieldSize x = p ^ f) :
    (order x).factorization p = f * characteristicExponent x := by
  have hpq : p ∣ fieldSize x := hq ▸ dvd_pow_self _ (by omega)
  rw [lie_order_eq hl, numerator, hq]
  exact characteristic_valuation hp (denominator_dvd_residual hx)
    (characteristic_not_dvd_residual hx hl hp hpq)

theorem characteristic_not_dvd_denominator {x : RawEntry} (hx : Admissible x)
    (hl : IsLie x) {p : ℕ} (hp : p.Prime) (hpq : p ∣ fieldSize x) :
    ¬ p ∣ denominator x :=
  fun h => characteristic_not_dvd_residual hx hl hp hpq (h.trans (denominator_dvd_residual hx))

end Atlas.OrderArithmetic
