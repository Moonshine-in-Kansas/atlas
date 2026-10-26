import Atlas.OrderArithmetic.PrimitiveExponentDivisibility
import Atlas.OrderArithmetic.SecondIndexBounds
import Mathlib.Tactic.SplitIfs

namespace Atlas.OrderArithmetic

/-- A proper primitive exponent below the largest index of a classical residual
lies at or below the numerical second index. This is a support theorem for a
supplied prime, not a primitive-prime existence theorem. -/
theorem primitiveDivisor_classical_second_gap
    {x : RawEntry} {p f h l : ℕ} (hx : Admissible x) (hc : IsClassicalLie x)
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hf : 1 ≤ f)
    (hfield : fieldSize x = p ^ f) (hbelow : h < f * topIndex x)
    (hres : l ∣ residual x) : h ≤ f * secondIndex x := by
  by_contra hn
  have hlarge : f * secondIndex x < h := by omega
  have hs := secondIndex_one_le hx hc
  have hh : 1 < h := by nlinarith
  have hminus : ∀ j : ℕ, 1 ≤ j →
      (j ≤ secondIndex x ∨
        (j = topIndex x ∧ topIndex x ≤ 2 * secondIndex x)) →
      ¬ l ∣ fieldSize x ^ j - 1 := by
    intro j hj hcases hd
    rw [hfield, ← pow_mul] at hd
    rcases hcases with hsmall | ⟨htop, hhalf⟩
    · have hb := primitiveDivisor_le_minus_index hp (by nlinarith : 0 < f * j) hd
      have hm := Nat.mul_le_mul_left f hsmall
      omega
    · have hdiv := (primitiveDivisor_dvd_minus_iff hp hpbase).mp hd
      obtain ⟨k, hk⟩ := hdiv
      have hlt : h < f * j := by simpa only [htop] using hbelow
      have hk2 : 2 ≤ k := by nlinarith [hp.1]
      have htwice : 2 * h ≤ f * j := by nlinarith
      have hm := Nat.mul_le_mul_left f hhalf
      rw [htop] at htwice
      nlinarith
  have hplus : ∀ j : ℕ, 1 ≤ j →
      (2 * j ≤ secondIndex x ∨
        (2 * j = topIndex x ∧ topIndex x ≤ 3 * secondIndex x)) →
      ¬ l ∣ fieldSize x ^ j + 1 := by
    intro j hj hcases hd
    rw [hfield, ← pow_mul] at hd
    rcases hcases with hsmall | ⟨htop, hthird⟩
    · have hb := primitiveDivisor_le_plus_index hp hpbase (by nlinarith : 0 < f * j) hd
      have hm := Nat.mul_le_mul_left f hsmall
      nlinarith
    · have hlt : h < 2 * (f * j) := by rw [← htop] at hbelow; nlinarith
      have hb := primitiveDivisor_proper_plus_index_bound hp hpbase hh hd hlt
      have hm := Nat.mul_le_mul_left f hthird
      rw [← htop] at hm
      nlinarith
  apply absurd hres
  cases x with
  | linear d q =>
    have hd := hx.1
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    apply hminus i (by omega)
    simp only [secondIndex, topIndex]
    omega
  | unitary d q =>
    have hd : 3 ≤ d := hx.1
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    unfold unitaryFactor
    split_ifs with hei
    · apply hminus i (by omega)
      apply Or.inl
      simp only [secondIndex]
      split_ifs <;> simp only [Nat.even_iff] at * <;> omega
    · apply hplus i (by omega)
      simp only [secondIndex, topIndex]
      split_ifs <;> simp only [Nat.even_iff] at * <;> omega
  | B r q | C r q =>
    have hr := hx.1
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    apply hminus (2 * i) (by omega)
    simp only [secondIndex, topIndex]
    omega
  | Dplus r q =>
    have hr := hx.1
    apply hp.2.1.prime.not_dvd_mul
    · apply hminus r (by omega)
      apply Or.inl
      simp only [secondIndex]
      omega
    · apply hp.2.1.prime.not_dvd_finsetProd
      intro i hi
      have hb := Finset.mem_Icc.mp hi
      apply hminus (2 * i) (by omega)
      simp only [secondIndex, topIndex]
      omega
  | Dminus r q =>
    have hr := hx.1
    apply hp.2.1.prime.not_dvd_mul
    · apply hplus r (by omega)
      apply Or.inr
      refine ⟨rfl, ?_⟩
      change 2 * r ≤ 3 * (2 * (r - 1))
      omega
    · apply hp.2.1.prime.not_dvd_finsetProd
      intro i hi
      have hb := Finset.mem_Icc.mp hi
      apply hminus (2 * i) (by omega)
      apply Or.inl
      simp only [secondIndex]
      omega
  | _ => simp_all [IsClassicalLie]

/-- The same gap holds for primitive prime divisors of the centrally divided
order; characteristic-power factors cannot contribute such a prime. -/
theorem primitiveDivisor_classical_order_second_gap
    {x : RawEntry} {p f h l : ℕ} (hx : Admissible x) (hc : IsClassicalLie x)
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hf : 1 ≤ f)
    (hfield : fieldSize x = p ^ f) (hbelow : h < f * topIndex x)
    (hd : l ∣ order x) : h ≤ f * secondIndex x := by
  have hn : l ∣ numerator x := hd.trans (by
    rw [lie_order_eq (classical_isLie hc)]
    exact Nat.div_dvd_of_dvd (denominator_dvd_numerator hx))
  change l ∣ fieldSize x ^ characteristicExponent x * residual x at hn
  rcases hp.2.1.dvd_mul.mp hn with hchar | hres
  · rw [hfield, ← pow_mul] at hchar
    exact (primitiveDivisor_not_dvd_power hp hpbase hchar).elim
  · exact primitiveDivisor_classical_second_gap hx hc hp hpbase hf hfield hbelow hres

end Atlas.OrderArithmetic
