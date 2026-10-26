import Atlas.OrderArithmetic.PrimitiveResidualBounds

namespace Atlas.OrderArithmetic
open scoped BigOperators

/-- A supplied primitive divisor at an even exponent occurs in the plus factor. -/
theorem primitiveDivisor_dvd_plus {p j l : ℕ}
    (hp : PrimitiveDivisor p (2 * j) l) (hpbase : 2 ≤ p) (hj : 0 < j) :
    l ∣ p ^ j + 1 := by
  have hu : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
  have hu2 : 1 ≤ (p ^ j) ^ 2 := Nat.one_le_pow _ _ hu
  have hs := Nat.sub_add_cancel hu
  have hs2 := Nat.sub_add_cancel hu2
  have hfactor : (p ^ j) ^ 2 - 1 = (p ^ j - 1) * (p ^ j + 1) := by nlinarith
  have hd := hp.2.2.1
  rw [Nat.mul_comm 2 j, pow_mul, hfactor] at hd
  exact (hp.2.1.dvd_mul.mp hd).resolve_left (hp.2.2.2 j hj (by omega))

/-- Every supplied primitive divisor at the top index occurs in the actual
residual formula. This establishes occurrence, without asserting existence. -/
theorem primitiveDivisor_top_dvd_residual {x : RawEntry} {p f l : ℕ}
    (hx : Admissible x) (hl : IsLie x)
    (hp : PrimitiveDivisor p (f * topIndex x) l) (hpbase : 2 ≤ p)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f) : l ∣ residual x := by
  have hminus : ∀ j : ℕ, topIndex x = j → l ∣ fieldSize x ^ j - 1 := by
    intro j hj
    rw [hfield, ← pow_mul, ← hj]
    exact hp.2.2.1
  have hplus : ∀ j : ℕ, 1 ≤ j → topIndex x = 2 * j →
      l ∣ fieldSize x ^ j + 1 := by
    intro j hj htop
    have he : f * topIndex x = 2 * (f * j) := by rw [htop]; ring
    have hprim : PrimitiveDivisor p (2 * (f * j)) l := he ▸ hp
    have hd := primitiveDivisor_dvd_plus hprim hpbase (by nlinarith : 0 < f * j)
    simpa only [hfield, ← pow_mul] using hd
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q =>
    exact (hminus d rfl).trans
      (Finset.dvd_prod_of_mem _ (show d ∈ Finset.Icc 2 d by simp [hx.1]))
  | unitary d q =>
    have hd : 3 ≤ d := hx.1
    by_cases he : Even d
    · have ho : ¬ Even (d - 1) := by
        rw [Nat.even_iff] at he ⊢
        omega
      have hfactor : l ∣ unitaryFactor q (d - 1) := by
        simp only [unitaryFactor, if_neg ho]
        exact hplus (d - 1) (by omega) (by simp [topIndex, he])
      exact hfactor.trans (Finset.dvd_prod_of_mem _
        (show d - 1 ∈ Finset.Icc 2 d by simp only [Finset.mem_Icc]; omega))
    · have hfactor : l ∣ unitaryFactor q d := by
        simp only [unitaryFactor, if_neg he]
        exact hplus d (by omega) (by simp [topIndex, he])
      exact hfactor.trans (Finset.dvd_prod_of_mem _
        (show d ∈ Finset.Icc 2 d by simp; omega))
  | B r q | C r q =>
    exact (hminus (2 * r) rfl).trans
      (Finset.dvd_prod_of_mem _ (show r ∈ Finset.Icc 1 r by simp; have := hx.1; omega))
  | Dplus r q =>
    have hr := hx.1
    apply dvd_mul_of_dvd_right
    exact (hminus (2 * (r - 1)) rfl).trans
      (Finset.dvd_prod_of_mem _
        (show r - 1 ∈ Finset.Icc 1 (r - 1) by simp; omega))
  | Dminus r q =>
    exact dvd_mul_of_dvd_left (hplus r (by have := hx.1; omega) rfl) _
  | F4 q | E6 q =>
    exact (hminus 12 rfl).trans (Finset.dvd_prod_of_mem _ (by simp))
  | E7 q =>
    exact (hminus 18 rfl).trans (Finset.dvd_prod_of_mem _ (by simp))
  | E8 q =>
    exact (hminus 30 rfl).trans (Finset.dvd_prod_of_mem _ (by simp))
  | G2 q => exact dvd_mul_of_dvd_left (hminus 6 rfl) _
  | twistedE6 q =>
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    exact dvd_mul_of_dvd_right (hplus 9 (by omega) rfl) _
  | trialityD4 q =>
    have hsmall : ¬ l ∣ q ^ 4 - 1 := by
      intro hd
      change q = p ^ f at hfield
      rw [hfield, ← pow_mul] at hd
      exact hp.2.2.2 (f * 4) (by nlinarith)
        (by simp only [topIndex]; nlinarith) hd
    have hfactor : q ^ 12 - 1 = (q ^ 8 + q ^ 4 + 1) * (q ^ 4 - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have h : (q ^ 8 + q ^ 4 + 1) * q ^ 4 + 1 =
          q ^ 12 + (q ^ 8 + q ^ 4 + 1) := by ring
      omega
    have hd := hminus 12 rfl
    change l ∣ q ^ 12 - 1 at hd
    rw [hfactor] at hd
    have hquartic := (hp.2.1.dvd_mul.mp hd).resolve_right hsmall
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hquartic _) _
  | suzuki q => exact dvd_mul_of_dvd_left (hplus 2 (by omega) rfl) _
  | smallRee q => exact dvd_mul_of_dvd_left (hplus 3 (by omega) rfl) _
  | largeRee q =>
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hplus 6 (by omega) rfl) _) _) _

/-- Above top index two, the supplied top divisor survives the central quotient. -/
theorem primitiveDivisor_top_dvd_order {x : RawEntry} {p f l : ℕ}
    (hx : Admissible x) (hl : IsLie x)
    (hp : PrimitiveDivisor p (f * topIndex x) l) (hpbase : 2 ≤ p)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f) (htop : 2 < topIndex x) :
    l ∣ order x := by
  exact primitiveDivisor_dvd_order hp hx hl
    (primitiveDivisor_top_dvd_residual hx hl hp hpbase hf hfield)
    (primitiveDivisor_not_dvd_denominator hp hx hl hf hfield (by nlinarith))

end Atlas.OrderArithmetic
