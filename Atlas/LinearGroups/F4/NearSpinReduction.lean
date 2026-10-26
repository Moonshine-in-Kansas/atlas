import Atlas.LinearGroups.F4.NearSpinRootMaps

/-! Explicit pivot reduction in the eight-dimensional near-spin coordinates.
This is an actual six-root word; no orthogonal recognition theorem is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

-- The six verified subgroup elements stay opaque while composing their actions.
attribute [local irreducible] nearStep

def nearAfterThree (v : Fin 8→F) : Fin 8→F :=
  nearStepSpin 2 (-v 6/v 0)
    (nearStepSpin 1 (v 5/v 0) (nearStepSpin 0 (-v 4/v 0) v))

def nearClearingWord (v : Fin 8→F) : parabolicPointStabilizer (F:=F) :=
  nearStep 5 (nearAfterThree v 3/v 0)*nearStep 4 (nearAfterThree v 2/v 0)*
    nearStep 3 (nearAfterThree v 1/v 0)*nearStep 2 (-v 6/v 0)*
      nearStep 1 (v 5/v 0)*nearStep 0 (-v 4/v 0)

def nearClearedSpin (v : Fin 8→F) : Fin 8→F :=
  nearStepSpin 5 (nearAfterThree v 3/v 0)
    (nearStepSpin 4 (nearAfterThree v 2/v 0)
      (nearStepSpin 3 (nearAfterThree v 1/v 0) (nearAfterThree v)))

theorem nearClearingWord_apply (c : F) (v : Fin 8→F) :
    (nearClearingWord v).val.val (nearVector c v)=nearVector c (nearClearedSpin v) := by
  change (nearStep 5 (nearAfterThree v 3/v 0)).val.val
    ((nearStep 4 (nearAfterThree v 2/v 0)).val.val
      ((nearStep 3 (nearAfterThree v 1/v 0)).val.val
        ((nearStep 2 (-v 6/v 0)).val.val
          ((nearStep 1 (v 5/v 0)).val.val
            ((nearStep 0 (-v 4/v 0)).val.val (nearVector c v))))))=_
  simp only [nearStep_apply]
  rfl

set_option maxHeartbeats 1200000 in
-- Six sparse shears reduce each of eight coordinates to a rational identity.
theorem nearClearedSpin_eq (v : Fin 8→F) (h : v 0≠0) :
    nearClearedSpin v=![v 0,0,0,0,0,0,0,nearQuadratic v/v 0] := by
  ext i
  fin_cases i <;>
    simp [nearClearedSpin,nearAfterThree,nearStepSpin,nearQuadratic] <;>
    field_simp [h] <;> ring

/-- Every near-spin isotropic vector with nonzero first coordinate is moved
onto its first coordinate axis by an actual marked-point stabilizer element. -/
theorem nearVector_reduce_pivot (c : F) (v : Fin 8→F)
    (h : v 0≠0) (hq : nearQuadratic v=0) :
    (nearClearingWord v).val.val (nearVector c v)=
      nearVector c (Pi.single 0 (v 0)) := by
  rw [nearClearingWord_apply,nearClearedSpin_eq v h,hq,zero_div]
  congr 1
  ext i; fin_cases i <;> simp [Pi.single_apply]

end Atlas.F4
