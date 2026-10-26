import Atlas.OrderArithmetic.MersenneArithmetic
import Atlas.OrderArithmetic.PrimeExponent
import Atlas.OrderArithmetic.FermatArithmetic

namespace Atlas.OrderArithmetic

/-- The Mersenne-side adjacent degree-two candidate always has larger order.
This inequality is uniform and does not require the Mersenne number to be prime. -/
theorem mersenne_adjacent_linear_two_lt {k : ℕ} (hk : 3 ≤ k) :
    order (.linear 2 (2 ^ k - 1)) < order (.linear 2 (2 ^ k)) := by
  have hq : 2 ≤ 2 ^ k := Nat.le_pow (by omega)
  have htq : 2 ^ (k - 1) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have he : Even (2 ^ k) := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
  rw [mersenne_linear_two_order hk, linear_two_even_order hq he]
  apply Nat.mul_lt_mul_of_pos_left _ (by omega)
  have hbound : (2 ^ k - 1) * (2 ^ (k - 1) - 1) ≤ (2 ^ k - 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left _ (by omega)
  have hsub : (2 ^ k - 1) + 1 = 2 ^ k := Nat.sub_add_cancel (by omega)
  have hsq : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsqsub := Nat.sub_add_cancel hsq
  have hstrict : (2 ^ k - 1) ^ 2 < (2 ^ k) ^ 2 - 1 := by nlinarith
  exact lt_of_le_of_lt hbound hstrict

/-- Once a competing label's characteristic is explicitly two, the infinite
Mersenne branch reduces to precisely L₂(7)/L₃(2). No characteristic-dominance
assumption is hidden in this theorem. -/
theorem mersenne_binary_characteristic_match {k f : ℕ} {x : RawEntry}
    (hp : (2 ^ k - 1).Prime) (hm : Admissible (.linear 2 (2 ^ k - 1)))
    (hx : Admissible x) (hl : IsLie x) (hf : 1 ≤ f)
    (hfield : fieldSize x = 2 ^ f)
    (he : order (.linear 2 (2 ^ k - 1)) = order x) :
    k = 3 ∧ x = .linear 3 2 := by
  have hk := mersenne_exponent_three_le hp hm
  have hv := order_characteristic_valuation hx hl (by decide : Nat.Prime 2) hf hfield
  rw [← he, mersenne_linear_two_valuation hk] at hv
  rcases mersenne_prime_product_split hp hv.symm with ⟨ha, hfk⟩ | ⟨hf1, ha⟩
  · obtain ⟨q, rfl⟩ := exponent_one_linear_two hx hl ha
    have hq : q = 2 ^ k := by simpa only [fieldSize, hfk] using hfield
    subst q
    exact ((mersenne_adjacent_linear_two_lt hk).ne he).elim
  · have hfield2 : fieldSize x = 2 := by simpa only [hf1, pow_one] using hfield
    have hprime : (characteristicExponent x).Prime := by
      rw [ha]
      exact mersenne_exponent_prime hp
    have hthree : 3 ≤ characteristicExponent x := by omega
    have hx3 := binary_prime_exponent_label hx hl hfield2 hprime hthree
    refine ⟨?_, hx3⟩
    rw [hx3] at ha
    norm_num [characteristicExponent] at ha
    omega

end Atlas.OrderArithmetic
