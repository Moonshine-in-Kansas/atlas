import Atlas.Fischer.OctadRealGrading

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The actual coordinate projection to one marked-octad real component. -/
def octadRealProjection (O : Octad) (S : Finset Omega) : RealCoordinates →ₗ[ℝ] RealCoordinates := by
  classical
  let P : (RationalCoordinateIndex → ℝ) →ₗ[ℝ] (RationalCoordinateIndex → ℝ) :=
    { toFun := fun f p => if octadRationalLabel O p = S then f p else 0
      map_add' := by intros; funext p; split <;> simp_all
      map_smul' := by intros; funext p; split <;> simp_all }
  exact realCoordinateEquiv.symm.toLinearMap.comp
    (P.comp realCoordinateEquiv.toLinearMap)

theorem octadRealProjection_coordinate (O : Octad) (S : Finset Omega)
    (x : RealCoordinates) (p : RationalCoordinateIndex) :
    realCoordinateEquiv (octadRealProjection O S x) p =
      if octadRationalLabel O p = S then realCoordinateEquiv x p else 0 := by
  classical
  exact congrFun (realCoordinateEquiv.apply_symm_apply _) p

theorem octadRealProjection_mem (O : Octad) (S : Finset Omega) (x : RealCoordinates) :
    octadRealProjection O S x ∈ octadRealGrade O S := by
  classical
  intro p hp
  rw [octadRealProjection_coordinate, if_neg hp]

theorem octadRealProjection_eq_self (O : Octad) (S : Finset Omega)
    {x : RealCoordinates} (hx : x ∈ octadRealGrade O S) :
    octadRealProjection O S x = x := by
  classical
  apply realCoordinateEquiv.injective
  funext p
  rw [octadRealProjection_coordinate]
  split
  · rfl
  · exact (hx p ‹_›).symm

theorem octadRealProjection_other (O : Octad) (S T : Finset Omega) (hST : S ≠ T)
    {x : RealCoordinates} (hx : x ∈ octadRealGrade O T) :
    octadRealProjection O S x = 0 := by
  classical
  apply realCoordinateEquiv.injective
  funext p
  rw [octadRealProjection_coordinate, map_zero, Pi.zero_apply]
  split
  · exact hx p (by simpa only [‹octadRationalLabel O p = S›] using hST)
  · rfl

/-- Every vector is the sum of its actual marked-octad real components. -/
theorem octadRealProjection_sum (O : Octad) (x : RealCoordinates) :
    (∑ S : Finset Omega, octadRealProjection O S x) = x := by
  classical
  apply realCoordinateEquiv.injective
  rw [map_sum]
  funext p
  simp only [Finset.sum_apply, octadRealProjection_coordinate]
  simp

end Atlas.Fischer
