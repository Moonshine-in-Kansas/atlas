import Atlas.LinearGroups.ReeF4.PositiveRootSubgroup
import Atlas.LinearGroups.ReeF4.SpecialLowestCharts
import Atlas.LinearGroups.ReeF4.SpecialMarkedPoints

/-! Fixation and an action, with no orbit or order assertion. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

section Coordinate
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem lowestRoot_weyl_read (d : WeylCoordinate) :
    weylCoordinateRead (rootVector (F := F) (0,0)) d =
      if d=(0,0) then 1 else 0 := by
  rcases d with ⟨b,j⟩
  fin_cases b <;> fin_cases j <;>
    simp [weylCoordinateRead,rootVector,wilsonCoordinatesEquiv,Pi.single_apply]

theorem AbsoluteUnitriangular.fixes_lowestRoot
    {e : TraceZero F ≃ₗ[F] TraceZero F} (he : AbsoluteUnitriangular e) :
    e (rootVector (F := F) (0,0))=rootVector (F := F) (0,0) := by
  apply weylCoordinateReadLinear_injective
  funext c
  change weylCoordinateRead (e (rootVector (F := F) (0,0))) c = _
  apply he
  intro d hd
  rw [lowestRoot_weyl_read]
  split_ifs with h
  · subst d
    have hc := (absoluteCoordinateGrade_bounds c).1
    change absoluteCoordinateGrade c < (-12 : ℤ) at hd
    omega
  · rfl

theorem AbsoluteUnitriangular.preserves_highestCoefficient
    {e : TraceZero F ≃ₗ[F] TraceZero F} (he : AbsoluteUnitriangular e)
    (u : TraceZero F) : (e u).val.2 0 7=u.val.2 0 7 := by
  change weylCoordinateRead (e u) (0,8)=weylCoordinateRead u (0,8)
  apply he
  intro d hd
  have hb := (absoluteCoordinateGrade_bounds d).2
  change (12 : ℤ) < absoluteCoordinateGrade d at hd
  omega
end Coordinate

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem positiveRootSubgroup_fixes_lowestRoot {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : positiveRootSubgroup hcard) :
    g.val.val (rootVector (F := F) (0,0))=rootVector (F := F) (0,0) :=
  (positiveRootSubgroup_le_unitriangular hcard g.property).fixes_lowestRoot

theorem positiveRootSubgroup_preserves_highestCoefficient {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : positiveRootSubgroup hcard)
    (u : TraceZero F) : (g.val.val u).val.2 0 7=u.val.2 0 7 :=
  (positiveRootSubgroup_le_unitriangular hcard g.property).preserves_highestCoefficient u

theorem positiveRootSubgroup_fixes_firstSpecialPoint {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : positiveRootSubgroup hcard) :
    g.val • firstSpecialPoint (F := F) m=firstSpecialPoint m := by
  change g.val • specialPointMk m (rootVector (F := F) (0,0)) _ = _
  rw [specialPointMk_smul]
  apply (specialPointMk_eq_iff m _ _ _ _).mpr
  refine ⟨1,?_⟩
  simpa only [one_smul] using (positiveRootSubgroup_fixes_lowestRoot hcard g).symm

private theorem highest_special_grade : ∀ j : Fin 26,
    specialAbsoluteGrade j ≤ specialAbsoluteGrade 9 := by decide

private def normalizedHighestChartOfRaw {m : ℕ} (u : TraceZero F)
    (hu : IsSpecialVector m u) (hn : u.val.2 0 7=1) :
    NormalizedSpecialChart (F := F) m 9 :=
  ⟨u,hu,hn,fun j hj => False.elim ((not_lt_of_ge (highest_special_grade j)) hj)⟩

/-- Actual action on the normalized top chart. No transitivity claim. -/
instance positiveRootNormalizedHighestAction {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    MulAction (positiveRootSubgroup hcard) (NormalizedSpecialChart (F := F) m 9) where
  smul g u := normalizedHighestChartOfRaw (g.val.val u.val)
    (u.property.1.map_model g.val)
    ((positiveRootSubgroup_preserves_highestCoefficient hcard g u.val).trans u.property.2.1)
  one_smul u := by
    apply Subtype.ext
    rfl
  mul_smul g h u := by
    apply Subtype.ext
    rfl

@[simp] theorem positiveRootNormalizedHighestAction_val {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : positiveRootSubgroup hcard)
    (u : NormalizedSpecialChart (F := F) m 9) :
    (g • u).val=g.val.val u.val := rfl

end Atlas.ReeF4
