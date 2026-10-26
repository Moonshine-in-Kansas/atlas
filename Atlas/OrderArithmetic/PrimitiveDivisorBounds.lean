import Atlas.OrderArithmetic.Valuations

namespace Atlas.OrderArithmetic

/-- A primitive prime divisor at a positive exponent. This is a predicate on a
supplied divisor, and does not assert that such a divisor always exists. -/
def PrimitiveDivisor (p h l : ℕ) : Prop :=
  0 < h ∧ l.Prime ∧ l ∣ p ^ h - 1 ∧
    ∀ j : ℕ, 0 < j → j < h → ¬ l ∣ p ^ j - 1

/-- A primitive divisor cannot divide its base. -/
theorem primitiveDivisor_not_dvd_base {p h l : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) : ¬ l ∣ p := by
  intro hd
  exact prime_not_dvd_pow_sub_one hp.2.1 hpbase hd hp.1 hp.2.2.1

/-- Consequently every characteristic-power factor is coprime to a supplied
primitive divisor, including the exponent-zero case. -/
theorem primitiveDivisor_not_dvd_power {p h l a : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) : ¬ l ∣ p ^ a := by
  intro hd
  exact primitiveDivisor_not_dvd_base hp hpbase (hp.2.1.dvd_of_dvd_pow hd)

/-- Exact central division preserves a prime residual divisor unless that prime
occurs in the denominator. -/
theorem prime_dvd_order_of_dvd_residual {x : RawEntry} {l : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hp : l.Prime)
    (hres : l ∣ residual x) (hden : ¬ l ∣ denominator x) : l ∣ order x := by
  have hn : l ∣ numerator x := dvd_mul_of_dvd_right hres _
  have he : order x * denominator x = numerator x := by
    rw [lie_order_eq hl]
    exact Nat.div_mul_cancel (denominator_dvd_numerator hx)
  rw [← he] at hn
  exact (hp.dvd_mul.mp hn).resolve_right hden

/-- A supplied primitive divisor survives into the order whenever it occurs in
the residual and is excluded from the central denominator. -/
theorem primitiveDivisor_dvd_order {p h l : ℕ} {x : RawEntry}
    (hp : PrimitiveDivisor p h l) (hx : Admissible x) (hl : IsLie x)
    (hres : l ∣ residual x) (hden : ¬ l ∣ denominator x) : l ∣ order x :=
  prime_dvd_order_of_dvd_residual hx hl hp.2.1 hres hden

/-- A minus factor containing a supplied primitive divisor cannot have smaller
positive exponent than its primitive index. -/
theorem primitiveDivisor_le_minus_index {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hj : 0 < j) (hd : l ∣ p ^ j - 1) : h ≤ j := by
  by_contra hlt
  exact hp.2.2.2 j hj (by omega) hd

/-- A plus factor can contain a supplied primitive divisor only up to twice
its exponent, by embedding it into the corresponding difference of squares. -/
theorem primitiveDivisor_le_plus_index {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hj : 0 < j)
    (hd : l ∣ p ^ j + 1) : h ≤ 2 * j := by
  have hu : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
  have hu2 : 1 ≤ (p ^ j) ^ 2 := Nat.one_le_pow _ _ hu
  have hsub := Nat.sub_add_cancel hu
  have hsub2 := Nat.sub_add_cancel hu2
  have hfactor : (p ^ j) ^ 2 - 1 = (p ^ j - 1) * (p ^ j + 1) := by nlinarith
  have hbig : l ∣ p ^ (2 * j) - 1 := by
    rw [Nat.mul_comm 2 j, pow_mul, hfactor]
    exact dvd_mul_of_dvd_right hd _
  exact primitiveDivisor_le_minus_index hp (by omega) hbig

/-- No central denominator can remove a supplied primitive divisor whose index
is strictly larger than twice the exponent of the label's field size. -/
theorem primitiveDivisor_not_dvd_denominator {p h l f : ℕ} {x : RawEntry}
    (hp : PrimitiveDivisor p h l) (hx : Admissible x) (hl : IsLie x)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f) (hlarge : 2 * f < h) :
    ¬ l ∣ denominator x := by
  intro hd
  have hbig := hd.trans (denominator_dvd_square_sub_one hx hl)
  rw [hfield, ← pow_mul, Nat.mul_comm f 2] at hbig
  have hbound := primitiveDivisor_le_minus_index hp (by omega : 0 < 2 * f) hbig
  omega

end Atlas.OrderArithmetic
