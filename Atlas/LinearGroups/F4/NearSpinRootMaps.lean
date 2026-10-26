import Atlas.LinearGroups.F4.NearPointGeometry
import Atlas.LinearGroups.F4.LeviLongRootImages

/-! Six actual B₃ Levi roots clear the six nonpivot coordinates of an
isotropic near-spin vector. All coefficients are ±1 in every characteristic. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def nearStep (k : Fin 6) (t : F) : parabolicPointStabilizer (F:=F) :=
  ![leviShortRoot 2 t,leviShortRoot 4 t,leviShortRoot 5 t,
    leviLongRoot 10 t,leviLongRoot 6 t,leviLongRoot 3 t] k

def nearStepSpin (k : Fin 6) (t : F) (v : Fin 8→F) : Fin 8→F :=
  ![![v 0,v 1 - t*v 5,v 2 - t*v 6,v 3,v 4 + t*v 0,v 5,v 6,v 7 - t*v 3],
    ![v 0,v 1 - t*v 4,v 2,v 3 - t*v 6,v 4,v 5 - t*v 0,v 6,v 7 + t*v 2],
    ![v 0,v 1,v 2 + t*v 4,v 3 - t*v 5,v 4,v 5,v 6 + t*v 0,v 7 + t*v 1],
    ![v 0,v 1 - t*v 0,v 2,v 3,v 4,v 5,v 6,v 7 - t*v 6],
    ![v 0,v 1,v 2 - t*v 0,v 3,v 4,v 5,v 6,v 7 + t*v 5],
    ![v 0,v 1,v 2,v 3 - t*v 0,v 4,v 5,v 6,v 7 + t*v 4]] k

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
-- Each of six sparse maps is selected before its coordinates are expanded.
theorem nearStep_apply (k : Fin 6) (t c : F) (v : Fin 8→F) :
    (nearStep k t).val.val (nearVector c v)=nearVector c (nearStepSpin k t v) := by
  fin_cases k
  all_goals
    simp only [nearStep,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ']
  · change shortRootLinear 3 t (nearVector c v)=_
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,shortRootLinear,
          shortRootFormula,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,shortRootLinear,
          shortRootFormula,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · change shortRootLinear 5 t (nearVector c v)=_
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,shortRootLinear,
          shortRootFormula,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,shortRootLinear,
          shortRootFormula,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · change shortRootLinear 6 t (nearVector c v)=_
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,shortRootLinear,
          shortRootFormula,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,shortRootLinear,
          shortRootFormula,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · change (longRoot (leviLongLabel 10) t).val (nearVector c v)=_
    rw [longRoot_leviLongApply]
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,leviLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,leviLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · change (longRoot (leviLongLabel 6) t).val (nearVector c v)=_
    rw [longRoot_leviLongApply]
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,leviLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,leviLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · change (longRoot (leviLongLabel 3) t).val (nearVector c v)=_
    rw [longRoot_leviLongApply]
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,leviLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,upperSpinEmbed,parabolicVector,nearStepSpin,leviLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring

end Atlas.F4
