import Atlas.LinearGroups.ReeF4.ShortRootStarCoefficients
import Atlas.LinearGroups.ReeF4.ShortRootExterior

/-! Full exterior-kernel compatibility of the candidate with the short-root operator. -/
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

theorem proposedStarLinear_shortRoot_marked (i j : TraceZeroCoordinate) :
    proposedStarLinear (wedge (shortRootLinear (markedBasis i))
      (shortRootLinear (markedBasis j))) =
    shortRootLinear (proposedStarLinear (F := F) (wedge (markedBasis i) (markedBasis j))) +
      shortRootStarCorrectionLinear (traceZeroCross (markedBasis i) (markedBasis j)) +
      shortRootStarPolarCorrectionLinear (traceZeroPolar (markedBasis i) (markedBasis j)) := by
  rw [shortRootLinear_basis, shortRootLinear_basis, shortRootImage_support,
    shortRootImage_support, star_wedge_lists, proposedStarLinear_marked_wedge]
  exact (shortRootStarCoefficient_eq i j).trans (by
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

theorem proposedStarLinear_shortRoot_defect :
    (proposedStarLinear (F := F)).comp (exteriorPower.map 2 shortRootLinear) =
      shortRootLinear.comp proposedStarLinear + shortRootStarCorrectionLinear.comp exteriorCross +
        shortRootStarPolarCorrectionLinear.comp exteriorPolar := by
  apply markedExteriorBasis.ext
  intro s
  simp only [LinearMap.comp_apply, LinearMap.add_apply, exterior_basis_wedge,
    exteriorCross_wedge, exteriorPolar_wedge]
  have hw (u v : TraceZero F) :
      exteriorPower.map 2 shortRootLinear (wedge u v) =
        wedge (shortRootLinear u) (shortRootLinear v) := by
    simp only [wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hw]
  exact proposedStarLinear_shortRoot_marked _ _

theorem proposedStarLinear_shortRoot_kernel (x : StarCarrier (F := F)) :
    proposedStarLinear (shortRootStarLinear x).val =
      shortRootLinear (proposedStarLinear x.val) := by
  change proposedStarLinear (exteriorPower.map 2 shortRootLinear x.val) =
    shortRootLinear (proposedStarLinear x.val)
  have h := LinearMap.congr_fun (proposedStarLinear_shortRoot_defect (F := F)) x.val
  have hc : exteriorCross x.val = 0 := x.property.2
  have hp : exteriorPolar x.val = 0 := x.property.1
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, hc, hp, _root_.map_zero, add_zero] using h

theorem proposedStarSemilinear_shortRoot (σ : F →+* F) (x : StarCarrier (F := F)) :
    proposedStarSemilinear σ (shortRootStarLinear x) =
      shortRootLinear (proposedStarSemilinear σ x) := by
  change traceZeroMap σ (proposedStarLinear (shortRootStarLinear x).val) =
    shortRootLinear (traceZeroMap σ (proposedStarLinear x.val))
  rw [proposedStarLinear_shortRoot_kernel, shortRootLinear_map]

theorem proposedPartialProduct_shortRoot (σ : F →+* F) (u v : TraceZero F)
    (h : StarDomain u v) :
    proposedPartialProduct σ (shortRootLinear u) (shortRootLinear v)
        ((starDomain_shortRoot_iff u v).mpr h) =
      shortRootLinear (proposedPartialProduct σ u v h) := by
  change proposedStarSemilinear σ _ = _
  rw [← shortRootStarLinear_domainWedge]
  exact proposedStarSemilinear_shortRoot σ _

end Atlas.ReeF4
