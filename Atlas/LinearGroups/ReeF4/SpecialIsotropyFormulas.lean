import Atlas.LinearGroups.ReeF4.SpecialIsotropyBilinear
import Atlas.LinearGroups.ReeF4.SpecialIsotropyCrossChecks.Row25

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
theorem isotropyCross_point (x y : Fin 26 → F) :
    isotropyCoordinates (traceZeroCross (isotropyPoint x) (isotropyPoint y)) =
      isotropyCross x y := by
  funext i
  fin_cases i
  · exact isotropyCross_component0 x y
  · exact isotropyCross_component1 x y
  · exact isotropyCross_component2 x y
  · exact isotropyCross_component3 x y
  · exact isotropyCross_component4 x y
  · exact isotropyCross_component5 x y
  · exact isotropyCross_component6 x y
  · exact isotropyCross_component7 x y
  · exact isotropyCross_component8 x y
  · exact isotropyCross_component9 x y
  · exact isotropyCross_component10 x y
  · exact isotropyCross_component11 x y
  · exact isotropyCross_component12 x y
  · exact isotropyCross_component13 x y
  · exact isotropyCross_component14 x y
  · exact isotropyCross_component15 x y
  · exact isotropyCross_component16 x y
  · exact isotropyCross_component17 x y
  · exact isotropyCross_component18 x y
  · exact isotropyCross_component19 x y
  · exact isotropyCross_component20 x y
  · exact isotropyCross_component21 x y
  · exact isotropyCross_component22 x y
  · exact isotropyCross_component23 x y
  · exact isotropyCross_component24 x y
  · exact isotropyCross_component25 x y

set_option maxHeartbeats 1200000 in
theorem isotropyPolar_point (x y : Fin 26 → F) :
    traceZeroPolar (isotropyPoint x) (isotropyPoint y)=isotropyPolar x y := by
  simp [Matrix.vecHead,Matrix.vecTail,traceZeroPolar,tracePairing,quadraticTrace,trace,isotropyPoint,isotropyPolar,
    SplitOctonion.norm,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem isotropyQuadratic_point (x : Fin 26 → F) :
    traceZeroQuadratic (isotropyPoint x)=isotropyQuadratic x := by
  simp [Matrix.vecHead,Matrix.vecTail,traceZeroQuadratic,quadraticTrace,isotropyPoint,isotropyQuadratic,
    SplitOctonion.norm,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem isotropyRawStar_actual (u v : TraceZero F) :
    isotropyCoordinates (proposedStarLinear (wedge u v)) =
      isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) :=
  isotropyRawStar_actual_bilinear u v

theorem isotropyCross_actual (u v : TraceZero F) :
    isotropyCoordinates (traceZeroCross u v) =
      isotropyCross (isotropyCoordinates u) (isotropyCoordinates v) := by
  simpa only [isotropyPoint_coordinates] using
    isotropyCross_point (isotropyCoordinates u) (isotropyCoordinates v)

theorem isotropyPolar_actual (u v : TraceZero F) :
    traceZeroPolar u v=isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v) := by
  simpa only [isotropyPoint_coordinates] using
    isotropyPolar_point (isotropyCoordinates u) (isotropyCoordinates v)

theorem isotropyQuadratic_actual (u : TraceZero F) :
    traceZeroQuadratic u=isotropyQuadratic (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using isotropyQuadratic_point (isotropyCoordinates u)

end Atlas.ReeF4
