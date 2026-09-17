import Atlas.Fischer.OctadRationalGradeCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The actual coordinate projection to one marked-octad rational component. -/
def octadRationalProjection (O : Octad) (S : Finset Omega) : Coordinates →ₗ[ℚ] Coordinates := by
  classical
  let P : (RationalCoordinateIndex → ℚ) →ₗ[ℚ] (RationalCoordinateIndex → ℚ) :=
    { toFun := fun f p => if octadRationalLabel O p = S then f p else 0
      map_add' := by intros; funext p; split <;> simp_all
      map_smul' := by intros; funext p; split <;> simp_all }
  exact rationalCoordinateEquiv.symm.toLinearMap.comp
    (P.comp rationalCoordinateEquiv.toLinearMap)

theorem octadRationalProjection_coordinate (O : Octad) (S : Finset Omega)
    (x : Coordinates) (p : RationalCoordinateIndex) :
    rationalCoordinateEquiv (octadRationalProjection O S x) p =
      if octadRationalLabel O p = S then rationalCoordinateEquiv x p else 0 := by
  classical
  exact congrFun (rationalCoordinateEquiv.apply_symm_apply _) p

theorem octadRationalProjection_mem (O : Octad) (S : Finset Omega) (x : Coordinates) :
    octadRationalProjection O S x ∈ octadRationalGrade O S := by
  classical
  intro p hp
  rw [octadRationalProjection_coordinate, if_neg hp]

theorem octadRationalProjection_eq_self (O : Octad) (S : Finset Omega)
    {x : Coordinates} (hx : x ∈ octadRationalGrade O S) :
    octadRationalProjection O S x = x := by
  classical
  apply rationalCoordinateEquiv.injective
  funext p
  rw [octadRationalProjection_coordinate]
  split
  · rfl
  · exact (hx p ‹_›).symm

theorem octadRationalProjection_other (O : Octad) (S T : Finset Omega) (hST : S ≠ T)
    {x : Coordinates} (hx : x ∈ octadRationalGrade O T) :
    octadRationalProjection O S x = 0 := by
  classical
  apply rationalCoordinateEquiv.injective
  funext p
  rw [octadRationalProjection_coordinate, map_zero, Pi.zero_apply]
  split
  · exact hx p (by simpa only [‹octadRationalLabel O p = S›] using hST)
  · rfl

/-- Every vector is the sum of its actual marked-octad rational components. -/
theorem octadRationalProjection_sum (O : Octad) (x : Coordinates) :
    (∑ S : Finset Omega, octadRationalProjection O S x) = x := by
  classical
  apply rationalCoordinateEquiv.injective
  rw [map_sum]
  funext p
  simp only [Finset.sum_apply, octadRationalProjection_coordinate]
  simp

end Atlas.Fischer
