import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot0
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot1
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot2
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot3
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot4
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot5
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot6
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulaRoot7

/-! Source-only aggregator. All 216 original row certificates remain in the
eight imported root modules. Coordinate helpers, scalar transport, universal
polynomial identity and actual field-valued root elements are unchanged. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

private theorem albertCoordinates_map {S : Type*} [CommRing S]
    (f : R →+* S) (x : Carrier R) (k : Fin 27) :
    albertCoordinates (Atlas.Albert.map f x) k = f (albertCoordinates x k) :=
  congrFun (Atlas.Albert.coordinate_map f x) (Atlas.F4.albertCoordinateOfFin k)

private theorem albertCoordinates_add (x y : Carrier R) (k : Fin 27) :
    albertCoordinates (x + y) k = albertCoordinates x k + albertCoordinates y k :=
  congrFun (_root_.map_add (coordinateEquiv (F := R)) x y)
    (Atlas.F4.albertCoordinateOfFin k)

private theorem albertCoordinates_smul (t : R) (x : Carrier R) (k : Fin 27) :
    albertCoordinates (t • x) k = t * albertCoordinates x k :=
  congrFun ((coordinateEquiv (F := R)).map_smul t x)
    (Atlas.F4.albertCoordinateOfFin k)

private theorem albertCoordinates_basis (j k : Fin 27) :
    albertCoordinates (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier R) k =
      if k = j then 1 else 0 := by
  have hi : Function.Injective Atlas.F4.albertCoordinateOfFin :=
    Atlas.F4.albertCoordinateFinEquiv.symm.injective
  simp only [albertCoordinates, coordinate_basisVector, Pi.single_apply, hi.eq_iff]

private theorem albertCoefficients_integral (i : Fin 8) (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient i (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleMatrix i k j ∧
      albertCoordinates
        (albertSecondCoefficient i (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier ℤ)) k =
        simpleSecondMatrix i k j := by
  fin_cases i
  · exact albertCoefficients_integral_root0 j k
  · exact albertCoefficients_integral_root1 j k
  · exact albertCoefficients_integral_root2 j k
  · exact albertCoefficients_integral_root3 j k
  · exact albertCoefficients_integral_root4 j k
  · exact albertCoefficients_integral_root5 j k
  · exact albertCoefficients_integral_root6 j k
  · exact albertCoefficients_integral_root7 j k

private theorem albertCoefficients_basis (i : Fin 8) (j k : Fin 27) :
    albertCoordinates
        (albertFirstCoefficient i (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier R)) k =
        (simpleMatrix i k j : R) ∧
      albertCoordinates
        (albertSecondCoefficient i (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier R)) k =
        (simpleSecondMatrix i k j : R) := by
  have hc := albertCoefficients_integral i j k
  constructor
  · have h := congrArg (Int.castRingHom R) hc.1
    rw [← albertCoordinates_map, ← albertFirstCoefficient_map,
      Atlas.Albert.map_basisVector] at h
    exact h
  · have h := congrArg (Int.castRingHom R) hc.2
    rw [← albertCoordinates_map, ← albertSecondCoefficient_map,
      Atlas.Albert.map_basisVector] at h
    exact h

private theorem albertSimple_ring_basis (i : Fin 8) (t : R) (j k : Fin 27) :
    albertCoordinates
      (albertSimpleApply i t
        (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier R)) k =
      simplePolynomialMatrix i t k j := by
  have h := congrArg (fun x : Carrier R => albertCoordinates x k)
    (albertSimple_parameter i t (basisVector (Atlas.F4.albertCoordinateOfFin j)))
  rw [albertCoordinates_add, albertCoordinates_add, albertCoordinates_smul,
    albertCoordinates_smul, albertCoordinates_basis,
    (albertCoefficients_basis (R := R) i j k).1,
    (albertCoefficients_basis (R := R) i j k).2] at h
  simpa only [simplePolynomialMatrix, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul] using h

/-- Universal integral-polynomial basis check, rather than values in small fields. -/
theorem albertSimple_polynomial_basis : ∀ (i : Fin 8) (j k : Fin 27),
    albertCoordinates
      (albertSimpleApply i Polynomial.X
        (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier (Polynomial ℤ))) k =
      simplePolynomialMatrix i Polynomial.X k j := by
  intro i j k
  exact albertSimple_ring_basis i Polynomial.X j k

noncomputable section Field
variable {F : Type*} [Field F]

/-- Elements of the pre-existing full norm-polynomial/unit stabilizer. -/
def albertSimple (i : Fin 8) (t : F) : Atlas.F4.Model F :=
  Fin.addCases (fun j => Atlas.F4.simplePositive j t)
    (fun j => Atlas.F4.simpleNegative j (-t)) i

attribute [local irreducible] Atlas.F4.simplePositive Atlas.F4.simpleNegative

theorem albertSimple_apply (i : Fin 8) (t : F) (x : Carrier F) :
    (albertSimple i t).val x = albertSimpleApply i t x := by
  fin_cases i
  · change (Atlas.F4.simplePositive (F := F) 0 t).val x =
      Atlas.F4.simplePositiveApply 0 t x
    exact Atlas.F4.simplePositive_apply (F := F) 0 t x
  · change (Atlas.F4.simplePositive (F := F) 1 t).val x =
      Atlas.F4.simplePositiveApply 1 t x
    exact Atlas.F4.simplePositive_apply (F := F) 1 t x
  · change (Atlas.F4.simplePositive (F := F) 2 t).val x =
      Atlas.F4.simplePositiveApply 2 t x
    exact Atlas.F4.simplePositive_apply (F := F) 2 t x
  · change (Atlas.F4.simplePositive (F := F) 3 t).val x =
      Atlas.F4.simplePositiveApply 3 t x
    exact Atlas.F4.simplePositive_apply (F := F) 3 t x
  · change (Atlas.F4.simpleNegative (F := F) 0 (-t)).val x =
      Atlas.F4.simpleNegativeApply 0 (-t) x
    exact Atlas.F4.simpleNegative_apply (F := F) 0 (-t) x
  · change (Atlas.F4.simpleNegative (F := F) 1 (-t)).val x =
      Atlas.F4.simpleNegativeApply 1 (-t) x
    exact Atlas.F4.simpleNegative_apply (F := F) 1 (-t) x
  · change (Atlas.F4.simpleNegative (F := F) 2 (-t)).val x =
      Atlas.F4.simpleNegativeApply 2 (-t) x
    exact Atlas.F4.simpleNegative_apply (F := F) 2 (-t) x
  · change (Atlas.F4.simpleNegative (F := F) 3 (-t)).val x =
      Atlas.F4.simpleNegativeApply 3 (-t) x
    exact Atlas.F4.simpleNegative_apply (F := F) 3 (-t) x

end Field
end Atlas.Chevalley.Comparison.F4
