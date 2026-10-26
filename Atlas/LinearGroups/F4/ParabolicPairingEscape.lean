import Atlas.Algebra.Albert.ShortRootPairing
import Atlas.LinearGroups.F4.ParabolicShortRoots
import Atlas.LinearGroups.F4.NearDetection

/-! Actual parabolic short roots detect every coordinate transverse to the
near nine-space. The displacement formula is uniform in all characteristics. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

private theorem cycleInverse_coordinate (p : Fin 3) (y : Carrier F) (i : Fin 8) :
    (((coordinateCycle (F:=F)^p.val)⁻¹).val y).2 2 i = y.2 (2-p) i := by
  fin_cases p
  · rfl
  · rfl
  · change (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
      (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle y)))).2 2 i = _
    rw [Atlas.Albert.coordinateCycle_three]
    rfl

theorem tracePairing_shortRoot (p : Fin 3) (i : Fin 8) (t : F) (y : Carrier F) :
    tracePairing y ((shortRoot p i t).val y) =
      tracePairing y y - t^2 * (y.2 (2-p) (7-i))^2 := by
  let g : Model F := coordinateCycle^p.val
  let z : Carrier F := (g⁻¹).val y
  have he : g.val z = y := g.val.apply_symm_apply y
  have h := stabilizer_tracePairing g z ((shortRootFirstPair i t).val z)
  rw [he] at h
  change tracePairing y ((shortRoot p i t).val y) =
    tracePairing z (shortRootLinear i t z) at h
  rw [h,tracePairing_shortRootLinear]
  have hz : tracePairing z z = tracePairing y y := stabilizer_tracePairing g⁻¹ y y
  rw [hz]
  rw [show z.2 2 (7-i) = y.2 (2-p) (7-i) from
    cycleInverse_coordinate p y (7-i)]

/-- Root labels corresponding to the fifteen transverse coordinates, in the
same order as `nonNearCoordinates`. -/
def nonNearDetectingRoot : Fin 15 → Fin 24 :=
  ![19,18,17,16,12,10,9,8,6,5,4,3,2,1,0]

theorem nonNearDetectingRoot_parabolic (i : Fin 15) :
    IsParabolicShort (nonNearDetectingRoot i) := by
  fin_cases i <;> decide +kernel

private theorem nonNearDetectingRoot_coordinate (i : Fin 15) (y : Carrier F) :
    y.2 (2-(shortRootPosition (nonNearDetectingRoot i)).1)
      (7-(shortRootPosition (nonNearDetectingRoot i)).2) = nonNearCoordinates y i := by
  fin_cases i <;> rfl

theorem parabolic_detecting_move (i : Fin 15) (y : Carrier F)
    (ha : adjoint y=0) (ht : trace y=0) (hi : nonNearCoordinates y i ≠ 0) :
    ∃ g : parabolicPointStabilizer (F:=F), tracePairing y (g.val.val y) ≠ 0 := by
  let r := nonNearDetectingRoot i
  let g : parabolicPointStabilizer (F:=F) :=
    ⟨shortRoot (shortRootPosition r).1 (shortRootPosition r).2 1,
      shortRoot_mem_parabolicPointStabilizer r (nonNearDetectingRoot_parabolic i) 1⟩
  refine ⟨g,?_⟩
  change tracePairing y ((shortRoot (shortRootPosition r).1
    (shortRootPosition r).2 1).val y) ≠ 0
  rw [tracePairing_shortRoot,nonNearDetectingRoot_coordinate i,
    tracePairing_self,ht,quadraticTrace_eq_zero_of_adjoint_eq_zero y ha]
  simpa using pow_ne_zero 2 hi

/-- Outside the near nine-space, a single actual point-stabilizer move makes
nonzero trace pairing with the starting white vector. -/
theorem nonnear_parabolic_self_pairing (y : Carrier F)
    (ha : adjoint y=0) (ht : trace y=0)
    (hy : y ∉ parabolicImageZero (F:=F)) :
    ∃ g : parabolicPointStabilizer (F:=F), tracePairing y (g.val.val y) ≠ 0 := by
  have hn : nonNearCoordinates y ≠ 0 := by
    intro h; exact hy (mem_near_of_nonNearCoordinates_zero y ha ht h)
  obtain ⟨i,hi⟩ : ∃i,nonNearCoordinates y i≠0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  exact parabolic_detecting_move i y ha ht hi

end Atlas.F4
