import Atlas.OrderArithmetic.BinaryCyclotomicProduct
import Atlas.OrderArithmetic.CyclotomicNoPrimitive
import Atlas.OrderArithmetic.BinarySmallTotient

namespace Atlas.OrderArithmetic
open Polynomial

/-- Convert the real finite-product estimate into the natural-number inequality
used by the exact binary remainder classification. -/
theorem binary_cyclotomic_value_bound {n l : ℕ} (hn : 0 < n)
    (he : ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs = l) :
    2 ^ n.totient < 4 * l := by
  have hbound := binary_cyclotomic_quarter_bound hn
  have habs : |(cyclotomic n ℤ).eval (2 : ℤ)| = (l : ℤ) := by
    rw [← Int.natCast_natAbs, he]
  have hintle : (cyclotomic n ℤ).eval (2 : ℤ) ≤ (l : ℤ) :=
    (le_abs_self _).trans_eq habs
  have hmap : (cyclotomic n ℝ).eval 2 = Int.cast ((cyclotomic n ℤ).eval (2 : ℤ)) := by
    simpa using cyclotomic.eval_apply (2 : ℤ) n (Int.castRingHom ℝ)
  have hreal_le : (cyclotomic n ℝ).eval 2 ≤ (l : ℝ) := by
    rw [hmap]
    exact_mod_cast hintle
  have hpos : 0 < (2 : ℝ) ^ n.totient := by positivity
  have hmul := (lt_div_iff₀ hpos).mp hbound
  have hreal : (2 : ℝ) ^ n.totient < 4 * (l : ℝ) := by linarith
  exact_mod_cast hreal

theorem binary_primitive_at_three : PrimitiveDivisor 2 3 7 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro j hj hlt
  interval_cases j <;> norm_num

theorem binary_primitive_at_four : PrimitiveDivisor 2 4 5 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro j hj hlt
  interval_cases j <;> norm_num

theorem binary_primitive_at_five : PrimitiveDivisor 2 5 31 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro j hj hlt
  interval_cases j <;> norm_num

theorem binary_primitive_at_ten : PrimitiveDivisor 2 10 11 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro j hj hlt
  interval_cases j <;> norm_num

/-- Binary primitive-divisor existence, with the unique index-six exception. -/
theorem binary_primitiveDivisor_exists {n : ℕ} (hn : 2 < n) (hne : n ≠ 6) :
    ∃ l : ℕ, PrimitiveDivisor 2 n l := by
  by_contra hno
  obtain ⟨l, hl, hln, he⟩ := cyclotomic_value_prime_of_no_primitive (by decide : 2 ≤ 2) hn hno
  have hdiv : l ∣ ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs := by
    change l ∣ ((cyclotomic n ℤ).eval ((2 : ℕ) : ℤ)).natAbs
    rw [he]
  have hmax : ∀ r : ℕ, r.Prime → r ∣ n → r ≤ l := by
    intro r hr hrd
    exact cyclotomic_prime_factor_dominates_index_primes (by omega) hl hdiv hr hrd
  have hsize := binary_cyclotomic_value_bound (by omega : 0 < n) he
  rcases binary_small_totient_indices hn hl hln hmax hsize with
    rfl | rfl | rfl | rfl | rfl
  · exact hno ⟨7, binary_primitive_at_three⟩
  · exact hno ⟨5, binary_primitive_at_four⟩
  · exact hno ⟨31, binary_primitive_at_five⟩
  · exact hne rfl
  · exact hno ⟨11, binary_primitive_at_ten⟩

/-- Primitive divisors exist for every integer base at least two and index
greater than two, apart from the binary index-six exception. -/
theorem primitiveDivisor_exists_of_index_gt_two {a n : ℕ}
    (ha : 2 ≤ a) (hn : 2 < n) (hexception : ¬ (a = 2 ∧ n = 6)) :
    ∃ l : ℕ, PrimitiveDivisor a n l := by
  by_cases ha2 : a = 2
  · subst a
    exact binary_primitiveDivisor_exists hn (fun hn6 => hexception ⟨rfl, hn6⟩)
  · exact primitiveDivisor_exists_of_base_ge_three (by omega) hn

/-- The excluded binary index really has no primitive prime divisor. -/
theorem binary_no_primitive_at_six : ¬ ∃ l : ℕ, PrimitiveDivisor 2 6 l := by
  rintro ⟨l, h⟩
  have hd : l ∣ 3 ^ 2 * 7 := by simpa using h.2.2.1
  rcases h.2.1.dvd_mul.mp hd with hd | hd
  · have he : l = 3 := (Nat.prime_dvd_prime_iff_eq h.2.1 (by decide)).mp
      (h.2.1.dvd_of_dvd_pow hd)
    subst l
    exact h.2.2.2 2 (by decide) (by decide) (by decide)
  · have he : l = 7 := (Nat.prime_dvd_prime_iff_eq h.2.1 (by decide)).mp hd
    subst l
    exact h.2.2.2 3 (by decide) (by decide) (by decide)

/-- Exact existence classification for all integer bases and indices above two. -/
theorem primitiveDivisor_exists_iff_of_index_gt_two {a n : ℕ}
    (ha : 2 ≤ a) (hn : 2 < n) :
    (∃ l : ℕ, PrimitiveDivisor a n l) ↔ ¬ (a = 2 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl⟩
    exact binary_no_primitive_at_six h
  · exact primitiveDivisor_exists_of_index_gt_two ha hn

end Atlas.OrderArithmetic
