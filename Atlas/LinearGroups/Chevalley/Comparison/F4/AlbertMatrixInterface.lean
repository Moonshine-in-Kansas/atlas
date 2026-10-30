import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertSimpleFormulas
import Atlas.LinearGroups.F4.SimpleCoroots
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
Source-only continuation of the saved `AlbertMatrices` interface, separated
from the integral conjugation checks. All matrices and root elements below
are the existing literal definitions. This file constructs the faithful
matrix representation of the full Albert stabilizer and identifies its eight
marked root matrices. It does not construct a Chevalley--Albert homomorphism.

Do not import the old candidate `Comparison.F4.AlbertMatrices` together with
this file: the common public declarations intentionally retain their names.
-/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix

section Scalars
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Naturality follows from the uniform parameter formula and the two
coefficient maps; no eight-entry tuple is expanded here. -/
theorem albertSimpleApply_map (f : R →+* S) (i : Fin 8) (t : R) (x : Carrier R) :
    albertSimpleApply i (f t) (Atlas.Albert.map f x) =
      Atlas.Albert.map f (albertSimpleApply i t x) := by
  simp only [albertSimple_parameter, Atlas.Albert.map_add,
    Atlas.F4.shortWeyl_map_smul, _root_.map_pow,
    albertFirstCoefficient_map, albertSecondCoefficient_map]

theorem albertCoordinates_map (f : R →+* S) (x : Carrier R) (j : Fin 27) :
    albertCoordinates (Atlas.Albert.map f x) j = f (albertCoordinates x j) :=
  congrFun (Atlas.Albert.coordinate_map f x) (Atlas.F4.albertCoordinateOfFin j)

theorem albertCoordinates_injective :
    Function.Injective (albertCoordinates (R := R)) := by
  intro x y h
  apply (Atlas.Albert.coordinateEquiv (F := R)).injective
  funext c
  obtain ⟨j, rfl⟩ := Atlas.F4.albertCoordinateFinEquiv.symm.surjective c
  exact congrFun h j

theorem simplePolynomialMatrix_map (f : R →+* S) (i : Fin 8) (t : R)
    (a c : Fin 27) :
    f (simplePolynomialMatrix i t a c) = simplePolynomialMatrix i (f t) a c := by
  simp [simplePolynomialMatrix, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, apply_ite]

/-- The universal polynomial column identity specializes to every
commutative ring, without interpolation or division. -/
theorem albertSimple_basis (i : Fin 8) (t : R) (j k : Fin 27) :
    albertCoordinates (albertSimpleApply i t
      (basisVector (Atlas.F4.albertCoordinateOfFin j) : Carrier R)) k =
      simplePolynomialMatrix i t k j := by
  let f : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) t
  have hf : f Polynomial.X = t := by simp [f]
  have h := congrArg f (albertSimple_polynomial_basis i j k)
  rw [← albertCoordinates_map, ← albertSimpleApply_map,
    Atlas.Albert.map_basisVector, hf, simplePolynomialMatrix_map, hf] at h
  exact h

end Scalars

section Field
variable (F : Type*) [Field F]

/-- The established coordinate order: three diagonal coordinates followed
by the three literal octonion coordinate blocks. -/
def albertReindex : Matrix Coordinate Coordinate F ≃+* Matrix (Fin 27) (Fin 27) F :=
  Matrix.reindexRingEquiv F Atlas.F4.albertCoordinateFinEquiv

/-- A representation of the full polynomial-and-unit stabilizer, not merely
the root-generated subgroup or a pointwise cubic stabilizer. -/
def albertMatrixHom : Atlas.F4.Model F →* Matrix (Fin 27) (Fin 27) F where
  toFun g := albertReindex F (matrixRepresentation g.val).val
  map_one' := by
    change albertReindex F (matrixRepresentation (1 : Carrier F ≃ₗ[F] Carrier F)).val = 1
    rw [_root_.map_one]
    exact _root_.map_one (albertReindex F)
  map_mul' g h := by
    change albertReindex F (matrixRepresentation (g.val * h.val)).val = _
    rw [_root_.map_mul]
    exact _root_.map_mul (albertReindex F) _ _

/-- Exact action on every Albert vector, with the same coordinate convention
as the literal integral matrices. -/
theorem albertMatrixHom_apply (g : Atlas.F4.Model F) (x : Carrier F) :
    albertMatrixHom F g *ᵥ albertCoordinates x = albertCoordinates (g.val x) := by
  change (matrixRepresentation g.val).val.submatrix
    Atlas.F4.albertCoordinateFinEquiv.symm
    Atlas.F4.albertCoordinateFinEquiv.symm *ᵥ albertCoordinates x = _
  rw [Matrix.submatrix_mulVec_equiv]
  have hc : albertCoordinates x ∘ Atlas.F4.albertCoordinateFinEquiv =
      coordinateEquiv x := by
    funext c
    exact congrArg (coordinateEquiv x)
      (Atlas.F4.albertCoordinateFinEquiv.symm_apply_apply c)
  rw [Equiv.symm_symm, hc, matrixRepresentation_apply]
  rfl

theorem albertMatrixHom_injective : Function.Injective (albertMatrixHom F) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply albertCoordinates_injective
  calc
    albertCoordinates (g.val x) = albertMatrixHom F g *ᵥ albertCoordinates x :=
      (albertMatrixHom_apply F g x).symm
    _ = albertMatrixHom F h *ᵥ albertCoordinates x :=
      congrArg (fun M : Matrix (Fin 27) (Fin 27) F => M *ᵥ albertCoordinates x) he
    _ = albertCoordinates (h.val x) := albertMatrixHom_apply F h x

theorem albertMatrixHom_column (g : Atlas.F4.Model F) (j k : Fin 27) :
    albertMatrixHom F g k j = albertCoordinates
      (g.val (basisVector (Atlas.F4.albertCoordinateOfFin j))) k := by
  have h := matrixRepresentation_apply g.val
    (basisVector (Atlas.F4.albertCoordinateOfFin j))
  rw [coordinate_basisVector, Matrix.mulVec_single_one] at h
  exact congrFun h (Atlas.F4.albertCoordinateOfFin k)

/-- The existing eight actual stabilizer elements have the exact saved
quadratic matrices. Negative indices already use minus the Wilson parameter. -/
theorem albertMatrixHom_simple (i : Fin 8) (t : F) :
    albertMatrixHom F (albertSimple i t) = simplePolynomialMatrix i t := by
  ext k j
  rw [albertMatrixHom_column, albertSimple_apply, albertSimple_basis]

theorem albertSimple_coordinates (i : Fin 8) (t : F) (x : Carrier F) :
    albertCoordinates (albertSimpleApply i t x) =
      simplePolynomialMatrix i t *ᵥ albertCoordinates x := by
  rw [← albertMatrixHom_simple F i t, ← albertSimple_apply]
  exact (albertMatrixHom_apply F (albertSimple i t) x).symm

/-- Reuse the public root-group laws; do not unfold the root constructions. -/
theorem albertSimple_add (i : Fin 8) (s t : F) :
    albertSimple i (s + t) = albertSimple i s * albertSimple i t := by
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ i
  · intro j
    simpa only [albertSimple, Fin.addCases_left] using
      (Atlas.F4.simplePositive_add (F := F) j s t).symm
  · intro j
    simpa only [albertSimple, Fin.addCases_right, neg_add] using
      (Atlas.F4.simpleNegative_add (F := F) j (-s) (-t)).symm

theorem albertSimple_zero (i : Fin 8) : albertSimple (F := F) i 0 = 1 := by
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ i
  · intro j
    simpa only [albertSimple, Fin.addCases_left] using
      Atlas.F4.simplePositive_zero (F := F) j
  · intro j
    simpa only [albertSimple, Fin.addCases_right, neg_zero] using
      Atlas.F4.simpleNegative_zero (F := F) j

theorem albertSimple_inv (i : Fin 8) (t : F) :
    (albertSimple i t)⁻¹ = albertSimple i (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← albertSimple_add, add_neg_cancel, albertSimple_zero]

/-- The inverse here is taken in the actual stabilizer, before applying its
matrix representation. No totalized matrix-inverse convention is used. -/
theorem albertMatrixHom_simple_inv (i : Fin 8) (t : F) :
    albertMatrixHom F ((albertSimple i t)⁻¹) = simplePolynomialMatrix i (-t) := by
  rw [albertSimple_inv, albertMatrixHom_simple]

/-- Both inverse products are certified through the existing group law. -/
theorem simplePolynomialMatrix_mul_neg (i : Fin 8) (t : F) :
    simplePolynomialMatrix i t * simplePolynomialMatrix i (-t) = 1 := by
  rw [← albertMatrixHom_simple F i t, ← albertMatrixHom_simple_inv F i t,
    ← _root_.map_mul, mul_inv_cancel, _root_.map_one]

theorem simplePolynomialMatrix_neg_mul (i : Fin 8) (t : F) :
    simplePolynomialMatrix i (-t) * simplePolynomialMatrix i t = 1 := by
  rw [← albertMatrixHom_simple_inv F i t, ← albertMatrixHom_simple F i t,
    ← _root_.map_mul, inv_mul_cancel, _root_.map_one]

end Field
end Atlas.Chevalley.Comparison.F4
