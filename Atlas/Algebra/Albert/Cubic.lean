import Atlas.Algebra.Albert.Coordinates
import Mathlib.Algebra.MvPolynomial.Eval

/-! An actual cubic polynomial, not a polynomial function on a finite field. -/
namespace Atlas.Albert
noncomputable section
variable {F : Type*} [CommRing F]

def universalVector : Carrier (MvPolynomial Coordinate F) :=
  (fun i => MvPolynomial.X (.inl i), fun i j => MvPolynomial.X (.inr (i,j)))

def normPolynomial : MvPolynomial Coordinate F := norm universalVector

theorem eval_normPolynomial (x : Carrier F) :
    MvPolynomial.eval (coordinateEquiv x) normPolynomial = norm x := by
  simp [normPolynomial, universalVector, norm, SplitOctonion.norm,
    SplitOctonion.trace, SplitOctonion.mul, coordinateEquiv]
  rfl

theorem norm_smul (t : F) (x : Carrier F) : norm (t • x) = t ^ 3 * norm x := by
  simp [norm, SplitOctonion.norm, SplitOctonion.trace, SplitOctonion.mul]
  ring

/-- A ring identity, hence also valid with an indeterminate parameter. -/
theorem norm_unit_add_smul (t : F) (x : Carrier F) :
    norm (unit + t • x) = 1 + t * trace x + t ^ 2 * quadraticTrace x +
      t ^ 3 * norm x := by
  simp [norm, trace, quadraticTrace, unit, SplitOctonion.norm,
    SplitOctonion.trace, SplitOctonion.mul]
  ring

end
end Atlas.Albert
