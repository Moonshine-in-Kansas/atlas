import Atlas.OrderArithmetic.ExceptionalPairCandidates
import Atlas.OrderArithmetic.ResidualPolynomial

namespace Atlas.OrderArithmetic

/-! Complete finite denominator rows for the exceptional-ratio branch.
No coefficient certificates or exclusion of roots are assumed in these rows. -/

structure ExceptionalPolynomialRow where
  left : RawEntry
  right : RawEntry
  leftDenominator : ℕ
  rightDenominator : ℕ
  deriving DecidableEq

def exceptionalPolynomialRows : Finset ExceptionalPolynomialRow :=
  exceptionalPairCandidates.biUnion fun pair =>
    (((centralBound pair.1).divisors).product (centralBound pair.2).divisors).image
      fun d => ⟨pair.1, pair.2, d.1, d.2⟩

set_option maxRecDepth 4096 in
theorem mem_exceptionalPolynomialRows {x y : RawEntry} {dx dy : ℕ}
    (hpair : (x, y) ∈ exceptionalPairCandidates)
    (hdx : dx ∈ (centralBound x).divisors) (hdy : dy ∈ (centralBound y).divisors) :
    (⟨x, y, dx, dy⟩ : ExceptionalPolynomialRow) ∈ exceptionalPolynomialRows := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(x, y), hpair, Finset.mem_image.mpr ?_⟩
  exact ⟨(dx, dy), Finset.mem_product.mpr ⟨hdx, hdy⟩, rfl⟩

set_option maxRecDepth 4096 in
/-- The concrete denominator choices from any admissible exceptional-ratio pair
occur among the finite rows, independently of its field sizes. -/
theorem actual_denominators_mem_exceptionalPolynomialRows {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hex : IsExceptionalLie x ∨ IsExceptionalLie y)
    (hratio : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x)
    (hne : withField x 0 ≠ withField y 0) :
    (⟨withField x 0, withField y 0, denominator x, denominator y⟩ : ExceptionalPolynomialRow)
      ∈ exceptionalPolynomialRows := by
  apply mem_exceptionalPolynomialRows
    (mem_exceptionalPairCandidates_of_ratio hx hy hlx hly hex hratio hne)
  · simpa only [centralBound_withField] using denominator_mem_centralBound_divisors hx
  · simpa only [centralBound_withField] using denominator_mem_centralBound_divisors hy

@[simp] theorem residualPolynomial_withField (x : RawEntry) (q : ℕ) :
    residualPolynomial (withField x q) = residualPolynomial x := by
  cases x <;> rfl

@[simp] theorem comparisonPolynomial_withField (x y : RawEntry) (q Q b a dx dy : ℕ) :
    comparisonPolynomial (withField x q) (withField y Q) b a dx dy =
      comparisonPolynomial x y b a dx dy := by
  simp only [comparisonPolynomial, residualPolynomial_withField]

def ExceptionalPolynomialRow.leftExponent (r : ExceptionalPolynomialRow) : ℕ :=
  characteristicExponent r.right /
    Nat.gcd (characteristicExponent r.left) (characteristicExponent r.right)

def ExceptionalPolynomialRow.rightExponent (r : ExceptionalPolynomialRow) : ℕ :=
  characteristicExponent r.left /
    Nat.gcd (characteristicExponent r.left) (characteristicExponent r.right)

noncomputable def ExceptionalPolynomialRow.polynomial (r : ExceptionalPolynomialRow) :
    Polynomial ℤ :=
  comparisonPolynomial r.left r.right r.leftExponent r.rightExponent
    r.leftDenominator r.rightDenominator

theorem actual_row_polynomial_eq (x y : RawEntry) :
    (⟨withField x 0, withField y 0, denominator x, denominator y⟩ : ExceptionalPolynomialRow).polynomial =
      comparisonPolynomial x y
        (characteristicExponent y / Nat.gcd (characteristicExponent x) (characteristicExponent y))
        (characteristicExponent x / Nat.gcd (characteristicExponent x) (characteristicExponent y))
        (denominator x) (denominator y) := by
  simp only [ExceptionalPolynomialRow.polynomial, ExceptionalPolynomialRow.leftExponent,
    ExceptionalPolynomialRow.rightExponent, characteristicExponent_withField,
    comparisonPolynomial_withField]

end Atlas.OrderArithmetic
