import Atlas.OrderArithmetic.AccumulatedValuation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.FieldTheory.Finite.Basic

namespace Atlas.OrderArithmetic

/-- Positive multiples of e up to d are parametrized without repetition by
the interval from zero to floor(d/e)-1. -/
theorem positive_multiples_image {e d : ℕ} (he : 1 ≤ e) :
    (Finset.Icc 1 d).filter (fun i => e ∣ i) =
      (Finset.range (d / e)).image (fun j => e * (j + 1)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hi, hid⟩, ⟨k, hik⟩⟩
    have hk : 1 ≤ k := by
      by_contra hh
      have hkzero : k = 0 := by omega
      rw [hkzero, mul_zero] at hik
      omega
    have hkd : k ≤ d / e := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith [hik])
    refine ⟨k - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hk]
    exact hik.symm
  · rintro ⟨j, hj, rfl⟩
    have hmul : (j + 1) * e ≤ d :=
      (Nat.le_div_iff_mul_le (by omega)).mp (by omega : j + 1 ≤ d / e)
    exact ⟨⟨by nlinarith, by nlinarith⟩, dvd_mul_right _ _⟩

/-- Reindex any sum supported on multiples of e. This combinatorial identity
is independent of prime valuations and group order formulas. -/
theorem sum_Icc_supported_on_multiples {e d : ℕ} (he : 1 ≤ e) (v : ℕ → ℕ)
    (hzero : ∀ i ∈ Finset.Icc 1 d, ¬ e ∣ i → v i = 0) :
    (∑ i ∈ Finset.Icc 1 d, v i) =
      ∑ j ∈ Finset.range (d / e), v (e * (j + 1)) := by
  have hs : (∑ i ∈ (Finset.Icc 1 d).filter (fun i => e ∣ i), v i) =
      ∑ i ∈ Finset.Icc 1 d, v i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    apply hzero i hi
    intro hd
    exact hn (Finset.mem_filter.mpr ⟨hi, hd⟩)
  rw [← hs, positive_multiples_image he, Finset.sum_image]
  intro i hi j hj hij
  nlinarith

/-- Once the support index is identified, the complete initial segment of
minus factors has exactly the accumulated block valuation. -/
theorem odd_prime_minus_segment_valuation {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hsupport : ∀ i : ℕ, 1 ≤ i → (l ∣ q ^ i - 1 ↔ e ∣ i)) (d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)).factorization l =
      (d / e) * (q ^ e - 1).factorization l + (d / e).factorial.factorization l := by
  have hnonzero : ∀ i ∈ Finset.Icc 1 d, q ^ i - 1 ≠ 0 := by
    intro i hi
    have hip := (Finset.mem_Icc.mp hi).1
    have hpow : q ≤ q ^ i := by simpa using Nat.pow_le_pow_right (by omega : 0 < q) hip
    omega
  have hblocknonzero : ∀ j ∈ Finset.range (d / e), q ^ (e * (j + 1)) - 1 ≠ 0 := by
    intro j hj
    have hpow : q ≤ q ^ (e * (j + 1)) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q)
        (by nlinarith : 1 ≤ e * (j + 1))
    omega
  have hdiv : l ∣ q ^ e - 1 := (hsupport e he).mpr (dvd_refl e)
  rw [Nat.factorization_prod_apply hnonzero,
    sum_Icc_supported_on_multiples he (fun i => (q ^ i - 1).factorization l)]
  · rw [← Nat.factorization_prod_apply hblocknonzero]
    exact odd_prime_minus_block_valuation hl hl2 hq he hdiv (d / e)
  · intro i hi hn
    exact Nat.factorization_eq_zero_of_not_dvd (fun hd =>
      hn ((hsupport i (Finset.mem_Icc.mp hi).1).mp hd))

/-- A uniform bound after exact support reindexing. The support condition is
an explicit input; no characteristic-dominance conclusion is assumed. -/
theorem odd_prime_minus_segment_contribution_le {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hsupport : ∀ i : ℕ, 1 ≤ i → (l ∣ q ^ i - 1 ↔ e ∣ i)) (d : ℕ) :
    l ^ (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)).factorization l ≤
      q ^ ((e + 1) * (d / e)) := by
  have hdiv : l ∣ q ^ e - 1 := (hsupport e he).mpr (dvd_refl e)
  rw [odd_prime_minus_segment_valuation hl hl2 hq he hsupport,
    ← odd_prime_minus_block_valuation hl hl2 hq he hdiv]
  exact odd_prime_minus_block_contribution_le_field_power hl hl2 hq he hdiv (d / e)

/-- The multiplicative order of the field-size residue gives the support
index automatically; no primitive-divisor existence hypothesis is needed. -/
theorem odd_cross_prime_minus_segment_contribution_le {l q : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q) (d : ℕ) :
    l ^ (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)).factorization l ≤ q ^ (2 * d) := by
  letI : Fact l.Prime := ⟨hl⟩
  let e := orderOf (q : ZMod l)
  have hn : (q : ZMod l) ≠ 0 := fun hh => hlq ((ZMod.natCast_eq_zero_iff q l).mp hh)
  have hediv : e ∣ l - 1 := ZMod.orderOf_dvd_card_sub_one hn
  have he : 1 ≤ e := Nat.pos_of_dvd_of_pos hediv (by have := hl.two_le; omega)
  have hs : ∀ i : ℕ, 1 ≤ i → (l ∣ q ^ i - 1 ↔ e ∣ i) := by
    intro i hi
    change l ∣ q ^ i - 1 ↔ orderOf (q : ZMod l) ∣ i
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff (q ^ i - 1) l,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 1 ≤ q)),
      Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  have hbound := odd_prime_minus_segment_contribution_le hl hl2 hq he hs d
  have het : e * (d / e) ≤ d := by
    have := Nat.div_mul_le_self d e
    nlinarith
  have ht : d / e ≤ d := Nat.div_le_self d e
  exact hbound.trans (Nat.pow_le_pow_right (by omega : 0 < q) (by nlinarith))

end Atlas.OrderArithmetic
