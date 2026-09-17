import Atlas.Fischer.ReflectingRootSymmetricSquares
import Atlas.Algebra.SymmetricMatrixProduct
import Atlas.Fischer.ProductMaps
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace Atlas.Fischer

/-- Conditional basis construction: the actual cardinal equality is kept explicit
until the independent displayed-family counting checkpoint supplies it. -/
def reflectingRootSquareBasis {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i)
    (hc : Fintype.card J = 306936) :
    Module.Basis J Scalar (Atlas.Algebra.symmetricMatrixSpace Scalar CoordinateIndex) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun j => Atlas.Algebra.symmetricMatrixSquare (r j))
    (reflectingRoot_symmetric_squares_independent r hr hd) (by
      rw [Atlas.Algebra.symmetricMatrixSpace_finrank, coordinateIndex_card, hc]
      norm_num [Nat.choose_two_right])

theorem reflectingRootSquareBasis_apply {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr hd hc) (j : J) :
    reflectingRootSquareBasis r hr hd hc j = Atlas.Algebra.symmetricMatrixSquare (r j) := by
  simp only [reflectingRootSquareBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- The retained product as a map conjugate-linear in both arguments. -/
def coordinateProductBisemilinear :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun := productRightMap
  map_add' x y := by apply LinearMap.ext; intro z; exact product_add_left x y z
  map_smul' a x := by apply LinearMap.ext; intro z; exact product_smul_left a x z

/-- A full reflecting-square basis determines any commutative conjugate-bilinear
product from the same intrinsic diagonal root equations. -/
theorem reflectingRoot_product_unique {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i)
    (hc : Fintype.card J = 306936)
    (B : Coordinates →ₛₗ[starRingEnd Scalar] Coordinates →ₛₗ[starRingEnd Scalar] Coordinates)
    (hB : ∀ x y, B x y = B y x)
    (he : ∀ j, B (r j) (r j) = (10 : Scalar) • r j) :
    ∀ x y, B x y = product x y := by
  classical
  have h := Atlas.Algebra.symmetricMatrixProduct_ext (starRingEnd Scalar)
    (reflectingRootSquareBasis r hr hd hc) r
    (reflectingRootSquareBasis_apply r hr hd hc) (by norm_num)
    B coordinateProductBisemilinear hB product_comm
    (fun j => (he j).trans (hr j).1.2.symm)
  intro x y
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end Atlas.Fischer
