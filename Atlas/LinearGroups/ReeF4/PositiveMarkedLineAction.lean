import Atlas.LinearGroups.ReeF4.MarkedLineStabilizerRestriction
import Atlas.LinearGroups.ReeF4.PositiveRootPointAction
import Atlas.LinearGroups.ReeF4.PositiveRootFactorList
import Atlas.LinearGroups.ReeF4.WeylRootTransport
import Atlas.LinearGroups.ReeF4.AlternatingShortRows0
import Atlas.LinearGroups.ReeF4.AlternatingShortRows1
import Atlas.LinearGroups.ReeF4.AlternatingShortRows2
import Atlas.LinearGroups.ReeF4.AlternatingShortRows3
import Atlas.LinearGroups.ReeF4.AlternatingLongRows0
import Atlas.LinearGroups.ReeF4.AlternatingLongRows1
import Atlas.LinearGroups.ReeF4.AlternatingLongRows2
import Atlas.LinearGroups.ReeF4.AlternatingLongRows3

/-!
Source-only, uncompiled. The positive subgroup acts on the actual marked line
by shears. In the retained alternating coordinates the shear is u 3, not u 0.
Only the existing first-coordinate root rows are used. No full-group order,
generation, transitivity, or assertion about the full line kernel is needed.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem markedLine_second_grade_le (c : WeylCoordinate) (hc : c ≠ (0,0)) :
    absoluteCoordinateGrade (2,0) ≤ absoluteCoordinateGrade c := by
  exact (by decide : ∀ c : WeylCoordinate, c ≠ (0,0) →
    absoluteCoordinateGrade (2,0) ≤ absoluteCoordinateGrade c) c hc

private theorem markedLine_read_combination (a b : F) (c : WeylCoordinate) :
    weylCoordinateRead (a • rootVector (F := F) (0,0) + b • rootVector (2,0)) c =
      a * (if c = (0,0) then 1 else 0) + b * (if c = (2,0) then 1 else 0) := by
  have h0 : weylCoordinateRead (rootVector (F := F) (0,0)) c =
      if c = (0,0) then 1 else 0 := weylCoordinateRead_root _ _
  have h2 : weylCoordinateRead (rootVector (F := F) (2,0)) c =
      if c = (2,0) then 1 else 0 := weylCoordinateRead_root _ _
  change (weylCoordinateReadLinear
    (a • rootVector (F := F) (0,0) + b • rootVector (2,0))) c = _
  rw [_root_.map_add, _root_.map_smul, _root_.map_smul]
  change a * weylCoordinateRead (rootVector (F := F) (0,0)) c +
    b * weylCoordinateRead (rootVector (F := F) (2,0)) c = _
  rw [h0, h2]

/-- The next-to-lowest weight vector can acquire only the lowest-root coefficient. -/
theorem AbsoluteUnitriangular.markedLine_second
    {e : TraceZero F ≃ₗ[F] TraceZero F} (he : AbsoluteUnitriangular e) :
    e (rootVector (F := F) (2,0)) =
      (e (rootVector (2,0))).val.2 0 0 • rootVector (0,0) + rootVector (2,0) := by
  apply weylCoordinateReadLinear_injective
  funext c
  change weylCoordinateRead (e (rootVector (F := F) (2,0))) c =
    weylCoordinateRead ((e (rootVector (2,0))).val.2 0 0 • rootVector (0,0) +
      rootVector (2,0)) c
  have hr := markedLine_read_combination
    ((e (rootVector (F := F) (2,0))).val.2 0 0) 1 c
  simp only [one_smul, one_mul] at hr
  rw [hr]
  by_cases hc : c = (0,0)
  · subst c
    simpa only [if_pos rfl, ite_true, ite_false,
      if_neg (show ((0,0) : WeylCoordinate) ≠ (2,0) by decide), mul_one, add_zero] using
      (show weylCoordinateRead (e (rootVector (F := F) (2,0))) (0,0) =
        (e (rootVector (2,0))).val.2 0 0 from rfl)
  · have hgrade := markedLine_second_grade_le c hc
    have hz : ∀ d, absoluteCoordinateGrade c < absoluteCoordinateGrade d →
        weylCoordinateRead (rootVector (F := F) (2,0)) d = 0 := by
      intro d hd
      rw [weylCoordinateRead_root]
      change (if d = (2,0) then (1 : F) else 0) = 0
      split_ifs with hd2
      · subst d
        exact False.elim ((not_lt_of_ge hgrade) hd)
      · rfl
    rw [he _ c hz, weylCoordinateRead_root]
    change (if c = (2,0) then (1 : F) else 0) =
      _ * (if c = (0,0) then 1 else 0) + (if c = (2,0) then 1 else 0)
    simp only [if_neg hc, mul_zero, zero_add]

theorem positiveRoot_markedLine_action {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (g : positiveRootSubgroup hcard) (a b : F) :
    g.val.val (specialMarkedLineVector a b) =
      specialMarkedLineVector
        (a + b * (g.val.val (rootVector (2,0))).val.2 0 0) b := by
  have h2 := (positiveRootSubgroup_le_unitriangular hcard g.property).markedLine_second
  rw [specialMarkedLineVector_eq, _root_.map_add, _root_.map_smul,
    _root_.map_smul, positiveRootSubgroup_fixes_lowestRoot hcard g]
  conv_lhs => rw [h2]
  rw [specialMarkedLineVector_eq]
  simp only [smul_add, smul_smul, add_smul, add_assoc]

theorem positiveRootSubgroup_le_markedLineStabilizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootSubgroup hcard ≤ markedLineStabilizer m := by
  have hm (g : positiveRootSubgroup hcard) {w : TraceZero F}
      (hw : w ∈ specialMarkedLine (F := F)) :
      g.val.val w ∈ specialMarkedLine (F := F) := by
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hw
    have he' : specialMarkedLineVector a b = w := (specialMarkedLineVector_eq a b).trans he
    rw [← he', positiveRoot_markedLine_action hcard g]
    exact (specialMarkedLineParam
      ![a + b * (g.val.val (rootVector (2,0))).val.2 0 0, b]).property
  intro g hg w
  constructor
  · exact hm ⟨g,hg⟩
  · intro hw
    have hi := hm (⟨g,hg⟩ : positiveRootSubgroup hcard)⁻¹ hw
    change g.val.symm (g.val w) ∈ specialMarkedLine (F := F) at hi
    simpa only [LinearEquiv.symm_apply_apply] using hi

/-- The actual inclusion of U into the already constructed full line stabilizer. -/
def positiveRootMarkedLineHom {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootSubgroup hcard →* markedLineStabilizer (F := F) m :=
  Subgroup.inclusion (positiveRootSubgroup_le_markedLineStabilizer hcard)

theorem positiveRootMarkedLineHom_injective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Injective (positiveRootMarkedLineHom hcard) :=
  Subgroup.inclusion_injective (positiveRootSubgroup_le_markedLineStabilizer hcard)

theorem positiveShortFactor_markedLine_second {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) (a b : F) :
    (positiveShortFactor hcard k a b).val (rootVector (F := F) (2,0)) =
      rootVector (2,0) := by
  have hc : ((positiveShortFactor hcard k a b).val
      (rootVector (F := F) (2,0))).val.2 0 0 = 0 := by
    rw [alternatingShortFactor_val]
    fin_cases k <;> simp only [Fin.reduceFinMk]
    · rw [alternatingShort_row_0_3]; simp [rootVector, Pi.single_apply]
    · rw [alternatingShort_row_1_3]; simp [rootVector, Pi.single_apply]
    · rw [alternatingShort_row_2_3]; simp [rootVector, Pi.single_apply]
    · rw [alternatingShort_row_3_3]; simp [rootVector, Pi.single_apply]
  simpa only [hc, zero_smul, zero_add] using
    (alternatingShortRoot_unitriangular hcard k
      (shortRootParameters m hcard (a,b))).markedLine_second

theorem positiveLongFactor_markedLine_second {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) (u : F) :
    (positiveLongFactor hcard k u).val (rootVector (F := F) (2,0)) =
      (if k = 3 then u else 0) • rootVector (0,0) + rootVector (2,0) := by
  have hc : ((positiveLongFactor hcard k u).val
      (rootVector (F := F) (2,0))).val.2 0 0 = if k = 3 then u else 0 := by
    rw [alternatingLongFactor_val]
    fin_cases k <;> simp only [Fin.reduceFinMk]
    · rw [alternatingLong_row_0_3]; simp [rootVector, Pi.single_apply]
    · rw [alternatingLong_row_1_3]; simp [rootVector, Pi.single_apply]
    · rw [alternatingLong_row_2_3]; simp [rootVector, Pi.single_apply]
    · rw [alternatingLong_row_3_3]; simp [rootVector, Pi.single_apply]
  simpa only [hc] using
    (alternatingLongRoot_unitriangular hcard k (Multiplicative.ofAdd u)).markedLine_second

private theorem positiveShortFactor_markedLine_sum {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) (a b t : F) :
    (positiveShortFactor hcard k a b).val
      (t • rootVector (F := F) (0,0) + rootVector (2,0)) =
      t • rootVector (0,0) + rootVector (2,0) := by
  rw [_root_.map_add, _root_.map_smul,
    (alternatingShortRoot_unitriangular hcard k
      (shortRootParameters m hcard (a,b))).fixes_lowestRoot,
    positiveShortFactor_markedLine_second]

private theorem positiveLongFactor_markedLine_sum {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) (u t : F) :
    (positiveLongFactor hcard k u).val
      (t • rootVector (F := F) (0,0) + rootVector (2,0)) =
      (t + if k = 3 then u else 0) • rootVector (0,0) + rootVector (2,0) := by
  rw [_root_.map_add, _root_.map_smul,
    (alternatingLongRoot_unitriangular hcard k (Multiplicative.ofAdd u)).fixes_lowestRoot,
    positiveLongFactor_markedLine_second, add_smul, add_assoc]

private theorem markedLine_model_mul_apply {m : ℕ} (g h : Model F m)
    (w : TraceZero F) : (g * h).val w = g.val (h.val w) := rfl

/-- The exact last long-root coordinate measures the action on the marked line. -/
theorem alternatingRootWord_markedLine_second {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (u : Fin 4 → F) (v : Fin 4 → F × F) :
    (alternatingRootWord hcard u v).val (rootVector (F := F) (2,0)) =
      u 3 • rootVector (0,0) + rootVector (2,0) := by
  have hw := congrArg (fun g : Model F m => g.val (rootVector (F := F) (2,0)))
    (positiveRootWord_expand hcard u v)
  simp only [markedLine_model_mul_apply] at hw
  exact hw.trans (by
    simp [positiveLongFactor_markedLine_second, positiveShortFactor_markedLine_sum,
      positiveLongFactor_markedLine_sum])

end Atlas.ReeF4
