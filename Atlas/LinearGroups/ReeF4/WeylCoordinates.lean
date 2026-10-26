import Atlas.LinearGroups.ReeF4.WilsonCoordinates

/-! Wilson R1 section 2's two coordinate involutions. Coordinates in each
block are ordered -4,-3,-2,-1,0,1,2,3,4. These maps do not yet assert
compatibility with the partial star product. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

/-- First source Weyl permutation, acting by pullback on Wilson coordinates. -/
def weylRhoCoordinates (w : WilsonCoordinates F) : WilsonCoordinates F :=
  ![![w 0 0, w 0 1, w 0 6, w 0 5, w 0 4, w 0 3, w 0 2, w 0 7, w 0 8],
    ![w 1 1, w 1 0, w 1 3, w 1 2, w 1 4, w 1 6, w 1 5, w 1 8, w 1 7],
    ![w 2 1, w 2 0, w 2 5, w 2 6, w 2 4, w 2 2, w 2 3, w 2 8, w 2 7]]

/-- Second source Weyl permutation; the scalar coordinates 0 and 2 exchange. -/
def weylSigmaCoordinates (w : WilsonCoordinates F) : WilsonCoordinates F :=
  ![![w 2 0, w 2 2, w 2 1, w 2 5, w 2 4, w 2 3, w 2 7, w 2 6, w 2 8],
    ![w 1 0, w 1 2, w 1 1, w 1 5, w 1 4, w 1 3, w 1 7, w 1 6, w 1 8],
    ![w 0 0, w 0 2, w 0 1, w 0 5, w 0 4, w 0 3, w 0 7, w 0 6, w 0 8]]

@[simp] theorem weylRhoCoordinates_involutive (w : WilsonCoordinates F) :
    weylRhoCoordinates (weylRhoCoordinates w) = w := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem weylSigmaCoordinates_involutive (w : WilsonCoordinates F) :
    weylSigmaCoordinates (weylSigmaCoordinates w) = w := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem weylRhoCoordinates_trace (w : WilsonCoordinates F) :
    wilsonTrace (weylRhoCoordinates w) = wilsonTrace w := rfl

@[simp] theorem weylSigmaCoordinates_trace (w : WilsonCoordinates F) :
    wilsonTrace (weylSigmaCoordinates w) = wilsonTrace w := by
  change w 2 4 + w 1 4 + w 0 4 = w 0 4 + w 1 4 + w 2 4
  ring

def weylRhoWilson : WilsonCoordinates F ≃ₗ[F] WilsonCoordinates F where
  toFun := weylRhoCoordinates
  invFun := weylRhoCoordinates
  left_inv := weylRhoCoordinates_involutive
  right_inv := weylRhoCoordinates_involutive
  map_add' x y := by funext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' a x := by funext i j; fin_cases i <;> fin_cases j <;> rfl

def weylSigmaWilson : WilsonCoordinates F ≃ₗ[F] WilsonCoordinates F where
  toFun := weylSigmaCoordinates
  invFun := weylSigmaCoordinates
  left_inv := weylSigmaCoordinates_involutive
  right_inv := weylSigmaCoordinates_involutive
  map_add' x y := by funext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' a x := by funext i j; fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 8192 in
/-- The product has exponent eight as an actual coordinate operator. -/
theorem weylWilson_product_pow_eight :
    ((weylRhoWilson (F := F)) * weylSigmaWilson) ^ 8 = 1 := by
  ext w i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem weylRhoWilson_square : (weylRhoWilson (F := F)) ^ 2 = 1 := by
  ext w i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem weylSigmaWilson_square : (weylSigmaWilson (F := F)) ^ 2 = 1 := by
  ext w i j
  fin_cases i <;> fin_cases j <;> rfl

end Atlas.ReeF4
