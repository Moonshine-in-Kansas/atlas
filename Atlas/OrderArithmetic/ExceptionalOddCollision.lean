import Atlas.OrderArithmetic.PolynomialRoots.All
import Atlas.OrderArithmetic.PolynomialComparison
import Atlas.OrderArithmetic.OddTopIndex

namespace Atlas.OrderArithmetic

/-! Exceptional-family comparison assembled from finite polynomial certificates.
The first theorem exposes the numerical ratio hypothesis for later reuse. The
odd-characteristic corollary derives that hypothesis from primitive divisors. -/

set_option maxRecDepth 8192 in
theorem exceptional_eq_of_equal_order_and_ratio {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hex : IsExceptionalLie x ∨ IsExceptionalLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y)
    (hratio : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x) : x = y := by
  by_cases ht : withField x 0 = withField y 0
  · exact same_template_equal_order_eq hx hy hlx hly hp hf hg hqx hqy he ht
  let r : ExceptionalPolynomialRow :=
    ⟨withField x 0, withField y 0, denominator x, denominator y⟩
  have hr : r ∈ exceptionalPolynomialRows :=
    actual_denominators_mem_exceptionalPolynomialRows hx hy hlx hly hex hratio ht
  obtain ⟨t, z, ht1, hz, hpz, hxz, hyz, hroot⟩ :=
    equal_order_polynomial_parameter hx hy hlx hly hp hf hg hqx hqy he
  have hleft : withField r.left (z ^ r.leftExponent) = x := by
    dsimp only [r, ExceptionalPolynomialRow.leftExponent]
    simp only [characteristicExponent_withField]
    rw [← hxz]
    simp only [withField_withField, withField_id]
  have hright : withField r.right (z ^ r.rightExponent) = y := by
    dsimp only [r, ExceptionalPolynomialRow.rightExponent]
    simp only [characteristicExponent_withField]
    rw [← hyz]
    simp only [withField_withField, withField_id]
  have ha : r.AdmissibleAt z := by
    unfold ExceptionalPolynomialRow.AdmissibleAt
    rw [hleft, hright]
    exact ⟨hx, hy⟩
  have hzero : r.polynomial.eval (z : ℤ) = 0 := by
    change (⟨withField x 0, withField y 0, denominator x, denominator y⟩ :
      ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0
    rw [actual_row_polynomial_eq]
    exact hroot
  exact (exceptionalPolynomialRows_admissible_no_root hr hz ha hzero).elim

/-- In a common odd characteristic, a pair involving an exceptional family can
have equal numerical orders only when its complete raw labels coincide. -/
theorem exceptional_eq_of_equal_order_odd_characteristic {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hex : IsExceptionalLie x ∨ IsExceptionalLie y)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) : x = y :=
  exceptional_eq_of_equal_order_and_ratio hx hy hlx hly hex hp hf hg hqx hqy he
    (exponent_top_ratio_of_equal_order_odd_characteristic hx hy hlx hly hp hp3 hf hg hqx hqy he)

end Atlas.OrderArithmetic
