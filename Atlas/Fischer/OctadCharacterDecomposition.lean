import Atlas.Fischer.OctadCommonEigenspaces

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

local instance octadCharacterLabelFintype (O : Octad) : Fintype (octadEvenCode O) :=
  Fintype.ofFinite _

theorem octadEvenCode_card (O : Octad) : Nat.card (octadEvenCode O) = 128 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit), octadEvenCode_finrank]
  simp [Bit]

/-- Projection indexed by the actual seven-dimensional character label space. -/
def octadCharacterProjection (O : Octad) (a : octadEvenCode O) :
    Coordinates →ₗ[ℚ] Coordinates := by
  classical
  let P : (RationalCoordinateIndex → ℚ) →ₗ[ℚ] (RationalCoordinateIndex → ℚ) :=
    { toFun := fun f p => if octadRationalCodeLabel O p = a then f p else 0
      map_add' := by intros; funext p; split <;> simp_all
      map_smul' := by intros; funext p; split <;> simp_all }
  exact rationalCoordinateEquiv.symm.toLinearMap.comp
    (P.comp rationalCoordinateEquiv.toLinearMap)

theorem octadCharacterProjection_coordinate (O : Octad) (a : octadEvenCode O)
    (x : Coordinates) (p : RationalCoordinateIndex) :
    rationalCoordinateEquiv (octadCharacterProjection O a x) p =
      if octadRationalCodeLabel O p = a then rationalCoordinateEquiv x p else 0 := by
  classical
  exact congrFun (rationalCoordinateEquiv.apply_symm_apply _) p

theorem octadCharacterProjection_eigenvector (O : Octad) (a : octadEvenCode O)
    (x : Coordinates) : OctadCommonEigenvector O a (octadCharacterProjection O a x) := by
  rw [octadCommonEigenvector_iff]
  intro p hp
  rw [octadCharacterProjection_coordinate, if_neg hp]

theorem octadCharacterProjection_eq_self (O : Octad) (a : octadEvenCode O)
    {x : Coordinates} (hx : OctadCommonEigenvector O a x) :
    octadCharacterProjection O a x = x := by
  classical
  rw [octadCommonEigenvector_iff] at hx
  apply rationalCoordinateEquiv.injective
  funext p
  rw [octadCharacterProjection_coordinate]
  split
  · rfl
  · exact (hx p ‹_›).symm

theorem octadCharacterProjection_other (O : Octad) (a b : octadEvenCode O) (hab : a ≠ b)
    {x : Coordinates} (hx : OctadCommonEigenvector O b x) :
    octadCharacterProjection O a x = 0 := by
  classical
  rw [octadCommonEigenvector_iff] at hx
  apply rationalCoordinateEquiv.injective
  funext p
  rw [octadCharacterProjection_coordinate, map_zero, Pi.zero_apply]
  split
  · exact hx p (by simpa only [‹octadRationalCodeLabel O p = a›] using hab)
  · rfl

/-- The actual algebra is the sum of its 128 cocode character components. -/
theorem octadCharacterProjection_sum (O : Octad) (x : Coordinates) :
    (∑ a : octadEvenCode O, octadCharacterProjection O a x) = x := by
  classical
  apply rationalCoordinateEquiv.injective
  rw [map_sum]
  funext p
  simp only [Finset.sum_apply, octadCharacterProjection_coordinate]
  simp

end Atlas.Fischer
