import Atlas.OrderArithmetic.Growth
import Atlas.OrderArithmetic.FactorialValuation

namespace Atlas.OrderArithmetic

/-- Complete unbounded reduction of alternating/Lie equality to degrees 5–19. -/
theorem alternating_lie_degree_bound {x : RawEntry} {n : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hn : 5 ≤ n)
    (h : order x = order (.alternating n)) : n < 20 :=
  alternating_degree_lt_twenty_of_growth hx hl hn h (order_growth hx hl)

/-- Only L₂ has characteristic exponent one in the admissible ordinary catalogue. -/
theorem exponent_one_linear_two {x : RawEntry} (hx : Admissible x) (hl : IsLie x)
    (ha : characteristicExponent x = 1) : ∃ q, x = .linear 2 q := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q =>
    have hd : 2 ≤ d := hx.1
    change d * (d - 1) / 2 = 1 at ha
    have hprod : d * (d - 1) ≤ 3 := by omega
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have : d = 2 := by nlinarith
    exact ⟨q, by rw [this]⟩
  | unitary d q =>
    have hd : 3 ≤ d := hx.1
    change d * (d - 1) / 2 = 1 at ha
    have hprod : d * (d - 1) ≤ 3 := by omega
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ d)
    nlinarith
  | B r q | C r q =>
    have hr : 2 ≤ r := hx.1
    change r ^ 2 = 1 at ha
    nlinarith
  | Dplus r q | Dminus r q =>
    have hr : 4 ≤ r := hx.1
    change r * (r - 1) = 1 at ha
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ r)
    nlinarith
  | _ => norm_num [characteristicExponent] at ha

/-- All admissible ordinary Lie values are composite, by their exact valuations. -/
theorem lie_order_not_prime {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    ¬ (order x).Prime := by
  intro hN
  obtain ⟨p, f, hp, hf, hq⟩ := lie_field_primePower hx hl
  have ha := characteristicExponent_pos hx hl
  have hv := order_characteristic_valuation hx hl hp hf hq
  have hd : p ∣ order x := (hp.dvd_iff_one_le_factorization hN.ne_zero).mpr (by rw [hv]; nlinarith)
  have hpN : p = order x := (hN.eq_one_or_self_of_dvd p hd).resolve_left hp.ne_one
  have hval : f * characteristicExponent x = 1 := by
    rw [← hpN, hp.factorization_self] at hv
    omega
  have he : characteristicExponent x = 1 := by nlinarith
  have hf1 : f = 1 := by nlinarith
  obtain ⟨q, rfl⟩ := exponent_one_linear_two hx hl he
  have hqp : q = p := by simpa [fieldSize, hf1] using hq
  subst q
  have hpp : 4 ≤ p := by
    have hsmall := hx.2.2
    have := hp.two_le
    simp only [true_and] at hsmall
    omega
  have hexact := Nat.div_mul_cancel (denominator_dvd_numerator hx)
  rw [← lie_order_eq hl, ← hpN] at hexact
  simp only [denominator, numerator, fieldSize, characteristicExponent, residual] at hexact
  norm_num [Finset.prod_Icc_succ_top] at hexact
  have hden : Nat.gcd 2 (p - 1) ≤ 2 := Nat.gcd_le_left _ (by omega)
  have hsq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsub := Nat.sub_add_cancel hsq
  have hlarge : 2 < p ^ 2 - 1 := by nlinarith
  have hlt := Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt hden hlarge) hp.pos
  omega

theorem cyclic_ne_lie {p : ℕ} {x : RawEntry} (hp : p.Prime)
    (hx : Admissible x) (hl : IsLie x) : order (.cyclic p) ≠ order x := by
  intro h
  change p = order x at h
  exact lie_order_not_prime hx hl (h ▸ hp)

end Atlas.OrderArithmetic
