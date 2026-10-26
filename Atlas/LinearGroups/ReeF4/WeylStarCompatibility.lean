import Atlas.LinearGroups.ReeF4.WeylSupport
import Atlas.LinearGroups.ReeF4.WeylStarCoefficients
import Atlas.LinearGroups.ReeF4.WeylExterior

/-! Full exterior-kernel compatibility of the candidate with the Weyl operators. -/
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

theorem proposedStarLinear_weyl_marked (g : Fin 2) (i j : TraceZeroCoordinate) :
    proposedStarLinear (wedge ((weylOperator g).toLinearMap (markedBasis i))
      ((weylOperator g).toLinearMap (markedBasis j))) =
    (weylOperator g).toLinearMap (proposedStarLinear (F := F) (wedge (markedBasis i) (markedBasis j))) +
      (weylStarCorrectionLinear g) (traceZeroCross (markedBasis i) (markedBasis j)) := by
  have hi : (weylOperator g).toLinearMap (markedBasis i) =
      ((weylSupport g i).map (starMarkedVector (F := F))).sum := by
    change weylOperator g (markedBasis i) = _
    rw [← starMarkedVector_basis i]
    exact weylOperator_support g i
  have hj : (weylOperator g).toLinearMap (markedBasis j) =
      ((weylSupport g j).map (starMarkedVector (F := F))).sum := by
    change weylOperator g (markedBasis j) = _
    rw [← starMarkedVector_basis j]
    exact weylOperator_support g j
  rw [hi, hj, star_wedge_lists, proposedStarLinear_marked_wedge]
  exact (weylStarCoefficient_eq g i j).trans (by
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

theorem proposedStarLinear_weyl_defect (g : Fin 2) :
    (proposedStarLinear (F := F)).comp (exteriorPower.map 2 (weylOperator g).toLinearMap) =
      (weylOperator g).toLinearMap.comp proposedStarLinear + (weylStarCorrectionLinear g).comp exteriorCross := by
  apply markedExteriorBasis.ext
  intro s
  simp only [LinearMap.comp_apply, LinearMap.add_apply, exterior_basis_wedge,
    exteriorCross_wedge]
  have hw (u v : TraceZero F) :
      exteriorPower.map 2 (weylOperator g).toLinearMap (wedge u v) =
        wedge ((weylOperator g).toLinearMap u) ((weylOperator g).toLinearMap v) := by
    simp only [wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hw]
  exact proposedStarLinear_weyl_marked g _ _

theorem proposedStarLinear_weyl_kernel (g : Fin 2) (x : StarCarrier (F := F)) :
    proposedStarLinear ((weylStarLinear g) x).val =
      (weylOperator g).toLinearMap (proposedStarLinear x.val) := by
  change proposedStarLinear (exteriorPower.map 2 (weylOperator g).toLinearMap x.val) =
    (weylOperator g).toLinearMap (proposedStarLinear x.val)
  have h := LinearMap.congr_fun (proposedStarLinear_weyl_defect (F := F) g) x.val
  have hc : exteriorCross x.val = 0 := x.property.2
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, hc, _root_.map_zero, add_zero] using h

theorem proposedStarSemilinear_weyl (g : Fin 2) (σ : F →+* F) (x : StarCarrier (F := F)) :
    proposedStarSemilinear σ ((weylStarLinear g) x) =
      (weylOperator g).toLinearMap (proposedStarSemilinear σ x) := by
  change traceZeroMap σ (proposedStarLinear ((weylStarLinear g) x).val) =
    (weylOperator g).toLinearMap (traceZeroMap σ (proposedStarLinear x.val))
  rw [proposedStarLinear_weyl_kernel]
  change traceZeroMap σ (weylOperator g (proposedStarLinear x.val)) =
    weylOperator g (traceZeroMap σ (proposedStarLinear x.val))
  exact weylOperator_map σ g _

theorem proposedPartialProduct_weyl (g : Fin 2) (σ : F →+* F) (u v : TraceZero F)
    (h : StarDomain u v) :
    proposedPartialProduct σ ((weylOperator g).toLinearMap u) ((weylOperator g).toLinearMap v)
        ((starDomain_weyl_iff g u v).mpr h) =
      (weylOperator g).toLinearMap (proposedPartialProduct σ u v h) := by
  change proposedStarSemilinear σ
      (domainWedge (weylOperator g u) (weylOperator g v) _) =
    weylOperator g (proposedStarSemilinear σ (domainWedge u v h))
  rw [← weylStarLinear_domainWedge]
  exact proposedStarSemilinear_weyl g σ _

end Atlas.ReeF4
