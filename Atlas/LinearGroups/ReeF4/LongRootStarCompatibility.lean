import Atlas.LinearGroups.ReeF4.LongRootStarCoefficients
import Atlas.LinearGroups.ReeF4.LongRootExterior

/-! Full exterior-kernel compatibility of the candidate with the long-root operator. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem wedge_zero_left (v : TraceZero F) : wedge 0 v = 0 := by
  have h := wedge_add_left (0 : TraceZero F) 0 v
  have he : wedge (0 : TraceZero F) v + 0 = wedge 0 v + wedge 0 v := by
    simpa only [zero_add, add_zero] using h
  exact (add_left_cancel he).symm

private theorem wedge_zero_right (v : TraceZero F) : wedge v 0 = 0 := by
  rw [wedge_comm_charTwo, wedge_zero_left]

private theorem star_wedge_lists (a b : List TraceZeroCoordinate) :
    proposedStarLinear (wedge ((a.map (starMarkedVector (F := F))).sum)
      ((b.map starMarkedVector).sum)) =
      (a.map (fun i => (b.map (extensionCoefficient i)).sum)).sum := by
  induction a with
  | nil => simp [wedge_zero_left]
  | cons i a ih =>
    simp only [List.map_cons, List.sum_cons, wedge_add_left, _root_.map_add, ih]
    congr 1
    clear ih
    induction b with
    | nil => simp [wedge_zero_right]
    | cons j b ihb =>
      simp only [List.map_cons, List.sum_cons, wedge_add_right, _root_.map_add,
        starMarkedVector_basis, proposedStarLinear_marked_wedge] at ihb ⊢
      rw [ihb]

theorem proposedStarLinear_longRoot_marked (i j : TraceZeroCoordinate) :
    proposedStarLinear (wedge (longRootLinear (markedBasis i))
      (longRootLinear (markedBasis j))) =
    longRootLinear (proposedStarLinear (F := F) (wedge (markedBasis i) (markedBasis j))) +
      longRootStarCorrectionLinear (traceZeroCross (markedBasis i) (markedBasis j)) := by
  rw [longRootLinear_basis, longRootLinear_basis, longRootImage_support,
    longRootImage_support, star_wedge_lists, proposedStarLinear_marked_wedge]
  exact (longRootStarCoefficient_eq i j).trans (by
    rw [starMarkedVector_basis, starMarkedVector_basis]
    rfl)

private theorem exterior_basis_wedge (s : ExteriorIndex) :
    markedExteriorBasis (F := F) s =
      wedge (markedBasis (exteriorLabel s 0)) (markedBasis (exteriorLabel s 1)) := by
  simp only [markedExteriorBasis, exteriorPower.coe_basis, exteriorPower.ιMulti_family,
    orderedMarkedBasis, Module.Basis.reindex_apply, exteriorLabel, wedge]
  congr 1
  funext k
  fin_cases k <;> simp [Function.comp_apply, Module.Basis.reindex_apply]

theorem proposedStarLinear_longRoot_defect :
    (proposedStarLinear (F := F)).comp (exteriorPower.map 2 longRootLinear) =
      longRootLinear.comp proposedStarLinear + longRootStarCorrectionLinear.comp exteriorCross := by
  apply markedExteriorBasis.ext
  intro s
  simp only [LinearMap.comp_apply, LinearMap.add_apply, exterior_basis_wedge,
    exteriorCross_wedge]
  have hw (u v : TraceZero F) :
      exteriorPower.map 2 longRootLinear (wedge u v) =
        wedge (longRootLinear u) (longRootLinear v) := by
    simp only [wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hw]
  exact proposedStarLinear_longRoot_marked _ _

theorem proposedStarLinear_longRoot_kernel (x : StarCarrier (F := F)) :
    proposedStarLinear (longRootStarLinear x).val =
      longRootLinear (proposedStarLinear x.val) := by
  change proposedStarLinear (exteriorPower.map 2 longRootLinear x.val) =
    longRootLinear (proposedStarLinear x.val)
  have h := LinearMap.congr_fun (proposedStarLinear_longRoot_defect (F := F)) x.val
  have hc : exteriorCross x.val = 0 := x.property.2
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, hc, _root_.map_zero, add_zero] using h

theorem proposedStarSemilinear_longRoot (σ : F →+* F) (x : StarCarrier (F := F)) :
    proposedStarSemilinear σ (longRootStarLinear x) =
      longRootLinear (proposedStarSemilinear σ x) := by
  change traceZeroMap σ (proposedStarLinear (longRootStarLinear x).val) =
    longRootLinear (traceZeroMap σ (proposedStarLinear x.val))
  rw [proposedStarLinear_longRoot_kernel, longRootLinear_map]

theorem proposedPartialProduct_longRoot (σ : F →+* F) (u v : TraceZero F)
    (h : StarDomain u v) :
    proposedPartialProduct σ (longRootLinear u) (longRootLinear v)
        ((starDomain_longRoot_iff u v).mpr h) =
      longRootLinear (proposedPartialProduct σ u v h) := by
  change proposedStarSemilinear σ _ = _
  rw [← longRootStarLinear_domainWedge]
  exact proposedStarSemilinear_longRoot σ _

end Atlas.ReeF4
