import Atlas.OrderArithmetic.PrimitiveTopDivisor

namespace Atlas.OrderArithmetic

/-- In the admissible Lie range, top index two means linear dimension two. -/
theorem topIndex_eq_two_linear_two {x : RawEntry} (hx : Admissible x)
    (hl : IsLie x) (ht : topIndex x = 2) : ∃ q, x = .linear 2 q := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q =>
    change d = 2 at ht
    exact ⟨q, by rw [ht]⟩
  | unitary d q =>
    have hd := hx.1
    simp only [topIndex] at ht
    split at ht <;> omega
  | B r q | C r q | Dplus r q | Dminus r q =>
    have hr := hx.1
    simp only [topIndex] at ht
    omega
  | _ => norm_num [topIndex] at ht

/-- The prime two cannot be primitive at an exponent greater than one. -/
theorem primitiveDivisor_ne_two {p h l : ℕ} (hp : PrimitiveDivisor p h l)
    (hpbase : 2 ≤ p) (hh : 1 < h) : l ≠ 2 := by
  intro he
  subst l
  have hn : ¬ 2 ∣ p := primitiveDivisor_not_dvd_base hp hpbase
  have hm : p % 2 ≠ 0 := by
    intro heq
    exact hn (Nat.dvd_of_mod_eq_zero heq)
  have hmod : p % 2 < 2 := Nat.mod_lt p (by decide)
  have hd : 2 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  exact hp.2.2.2 1 (by omega) hh (by simpa only [pow_one] using hd)

/-- Supplied top divisors survive even in linear dimension two once the scaled
top index exceeds two. The central divisor there is a divisor of two. -/
theorem primitiveDivisor_top_dvd_order_of_scaled_gt_two
    {x : RawEntry} {p f l : ℕ} (hx : Admissible x) (hl : IsLie x)
    (hp : PrimitiveDivisor p (f * topIndex x) l) (hpbase : 2 ≤ p)
    (hf : 1 ≤ f) (hfield : fieldSize x = p ^ f)
    (hscaled : 2 < f * topIndex x) : l ∣ order x := by
  by_cases htop : 2 < topIndex x
  · exact primitiveDivisor_top_dvd_order hx hl hp hpbase hf hfield htop
  have ht : topIndex x = 2 := by have := topIndex_two_le hx hl; omega
  have hd : denominator x ∣ 2 := by
    obtain ⟨q, rfl⟩ := topIndex_eq_two_linear_two hx hl ht
    exact Nat.gcd_dvd_left _ _
  apply primitiveDivisor_dvd_order hp hx hl
    (primitiveDivisor_top_dvd_residual hx hl hp hpbase hf hfield)
  intro hden
  have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hp.2.1 (by decide : Nat.Prime 2)).mp
    (hden.trans hd)
  exact primitiveDivisor_ne_two hp hpbase (by omega) hl2

/-- An equal-order competitor cannot have a smaller scaled top index when a
primitive divisor at the larger index has been explicitly supplied. -/
theorem scaled_topIndex_le_of_equal_order_and_primitive
    {x y : RawEntry} {p f g l : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hpbase : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hfx : fieldSize x = p ^ f) (hgy : fieldSize y = p ^ g)
    (he : order x = order y) (hscaled : 2 < f * topIndex x)
    (hp : PrimitiveDivisor p (f * topIndex x) l) :
    f * topIndex x ≤ g * topIndex y := by
  by_contra hnot
  have hxdiv := primitiveDivisor_top_dvd_order_of_scaled_gt_two hx hlx hp hpbase hf hfx hscaled
  rw [he] at hxdiv
  exact primitiveDivisor_not_dvd_order_of_large_index hy hly hp hpbase hg hgy
    (by omega) hxdiv

/-- Two supplied top divisors force equality of the scaled top indices. The
primitive-divisor existence obligations remain explicit. -/
theorem scaled_topIndex_eq_of_equal_order_and_primitives
    {x y : RawEntry} {p f g l m : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hpbase : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hfx : fieldSize x = p ^ f) (hgy : fieldSize y = p ^ g)
    (he : order x = order y) (hsx : 2 < f * topIndex x) (hsy : 2 < g * topIndex y)
    (hpx : PrimitiveDivisor p (f * topIndex x) l)
    (hpy : PrimitiveDivisor p (g * topIndex y) m) :
    f * topIndex x = g * topIndex y := by
  exact Nat.le_antisymm
    (scaled_topIndex_le_of_equal_order_and_primitive hx hy hlx hly hpbase hf hg hfx hgy he hsx hpx)
    (scaled_topIndex_le_of_equal_order_and_primitive hy hx hly hlx hpbase hg hf hgy hfx he.symm hsy hpy)

end Atlas.OrderArithmetic
