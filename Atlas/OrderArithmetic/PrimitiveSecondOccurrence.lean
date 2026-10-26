import Atlas.OrderArithmetic.PrimitiveTopDivisor
import Atlas.OrderArithmetic.PrimitiveExponentDivisibility
import Atlas.OrderArithmetic.SecondIndexBounds

namespace Atlas.OrderArithmetic
open scoped BigOperators

/-- A supplied primitive divisor at the second profile index occurs in the
actual residual of every admissible classical label. -/
theorem primitiveDivisor_second_dvd_residual {x : RawEntry} {p f l : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x)
    (hp : PrimitiveDivisor p (f * secondIndex x) l) (hpbase : 2 ≤ p)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f) : l ∣ residual x := by
  have hminus : ∀ j : ℕ, secondIndex x = j → l ∣ fieldSize x ^ j - 1 := by
    intro j hj
    rw [hfield, ← pow_mul, ← hj]
    exact hp.2.2.1
  have hplus : ∀ j : ℕ, 1 ≤ j → secondIndex x = 2 * j →
      l ∣ fieldSize x ^ j + 1 := by
    intro j hj hindex
    have he : f * secondIndex x = 2 * (f * j) := by rw [hindex]; ring
    have hprim : PrimitiveDivisor p (2 * (f * j)) l := he ▸ hp
    have hd := primitiveDivisor_dvd_plus hprim hpbase (by nlinarith : 0 < f * j)
    simpa only [hfield, ← pow_mul] using hd
  cases x with
  | linear d q =>
    have hd := hx.1
    by_cases hd2 : d = 2
    · subst d
      have hsmall : l ∣ q - 1 := by simpa only [fieldSize, pow_one] using hminus 1 rfl
      have hsquare : l ∣ q ^ 2 - 1 := hsmall.trans (Nat.sub_one_dvd_pow_sub_one q 2)
      simpa [residual] using hsquare
    · exact (hminus (d - 1) rfl).trans (Finset.dvd_prod_of_mem _
        (show d - 1 ∈ Finset.Icc 2 d by simp only [Finset.mem_Icc]; omega))
  | unitary d q =>
    have hd := hx.1
    by_cases hd3 : d = 3
    · subst d
      have hfactor : l ∣ unitaryFactor q 2 := by
        simpa [unitaryFactor, fieldSize] using hminus 2 rfl
      exact hfactor.trans (Finset.dvd_prod_of_mem _ (by decide : 2 ∈ Finset.Icc 2 3))
    by_cases hd4 : d = 4
    · subst d
      have hfactor : l ∣ unitaryFactor q 4 := by
        simpa [unitaryFactor, fieldSize, show Even 4 by decide] using hminus 4 rfl
      exact hfactor.trans (Finset.dvd_prod_of_mem _ (by decide : 4 ∈ Finset.Icc 2 4))
    by_cases hed : Even d
    · have hodd : ¬ Even (d - 3) := by
        rw [Nat.even_iff] at hed ⊢
        omega
      have hfactor : l ∣ unitaryFactor q (d - 3) := by
        simp only [unitaryFactor, if_neg hodd]
        exact hplus (d - 3) (by omega) (by simp [secondIndex, hd3, hd4, hed])
      exact hfactor.trans (Finset.dvd_prod_of_mem _
        (show d - 3 ∈ Finset.Icc 2 d by simp only [Finset.mem_Icc]; omega))
    · have hodd : ¬ Even (d - 2) := by
        rw [Nat.even_iff] at hed ⊢
        omega
      have hfactor : l ∣ unitaryFactor q (d - 2) := by
        simp only [unitaryFactor, if_neg hodd]
        exact hplus (d - 2) (by omega) (by simp [secondIndex, hd3, hd4, hed])
      exact hfactor.trans (Finset.dvd_prod_of_mem _
        (show d - 2 ∈ Finset.Icc 2 d by simp only [Finset.mem_Icc]; omega))
  | B r q | C r q =>
    have hr := hx.1
    exact (hminus (2 * (r - 1)) rfl).trans (Finset.dvd_prod_of_mem _
      (show r - 1 ∈ Finset.Icc 1 r by simp only [Finset.mem_Icc]; omega))
  | Dplus r q =>
    have hr := hx.1
    apply dvd_mul_of_dvd_right
    exact (hminus (2 * (r - 2)) rfl).trans (Finset.dvd_prod_of_mem _
      (show r - 2 ∈ Finset.Icc 1 (r - 1) by simp only [Finset.mem_Icc]; omega))
  | Dminus r q =>
    have hr := hx.1
    apply dvd_mul_of_dvd_right
    exact (hminus (2 * (r - 1)) rfl).trans (Finset.dvd_prod_of_mem _
      (show r - 1 ∈ Finset.Icc 1 (r - 1) by simp only [Finset.mem_Icc]; omega))
  | _ => simp_all [IsClassicalLie]

private theorem denominator_le_three_of_small_second {x : RawEntry}
    (hx : Admissible x) (hc : IsClassicalLie x) (hs : secondIndex x ≤ 2) :
    denominator x ≤ 3 := by
  cases x with
  | linear d q =>
    have hd := hx.1
    have hden : denominator (.linear d q) ≤ d := Nat.gcd_le_left _ (by omega)
    simp only [secondIndex] at hs
    omega
  | unitary d q =>
    have hd := hx.1
    have hden : denominator (.unitary d q) ≤ d := Nat.gcd_le_left _ (by omega)
    simp only [secondIndex] at hs
    split_ifs at hs <;> omega
  | B r q | C r q =>
    exact (Nat.gcd_le_left _ (by decide : 0 < 2)).trans (by omega)
  | Dplus r q | Dminus r q =>
    have hr := hx.1
    simp only [secondIndex] at hs
    omega
  | _ => simp_all [IsClassicalLie]

/-- Second-index primitive divisors above scaled index two survive every
classical central divisor, including the small linear/unitary ranks. -/
theorem primitiveDivisor_second_not_dvd_denominator {x : RawEntry} {p f l : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x)
    (hp : PrimitiveDivisor p (f * secondIndex x) l) (hpbase : 2 ≤ p)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f) (hs : 2 < f * secondIndex x) :
    ¬ l ∣ denominator x := by
  by_cases hsecond : 2 < secondIndex x
  · exact primitiveDivisor_not_dvd_denominator hp hx (classical_isLie hc) hf hfield (by nlinarith)
  · intro hd
    have hbound := denominator_le_three_of_small_second hx hc (by omega)
    have hle := Nat.le_of_dvd (denominator_pos hx) hd
    have hprime := primitiveDivisor_index_lt_prime hp hpbase
    omega

/-- A supplied primitive prime at a classical scaled second index greater than
two divides the actual order formula. -/
theorem primitiveDivisor_second_dvd_order {x : RawEntry} {p f l : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x)
    (hp : PrimitiveDivisor p (f * secondIndex x) l) (hpbase : 2 ≤ p)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f) (hs : 2 < f * secondIndex x) :
    l ∣ order x := by
  exact primitiveDivisor_dvd_order hp hx (classical_isLie hc)
    (primitiveDivisor_second_dvd_residual hx hc hp hpbase hf hfield)
    (primitiveDivisor_second_not_dvd_denominator hx hc hp hpbase hf hfield hs)

end Atlas.OrderArithmetic
