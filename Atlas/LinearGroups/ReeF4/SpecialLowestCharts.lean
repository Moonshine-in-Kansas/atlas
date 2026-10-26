import Atlas.LinearGroups.ReeF4.SpecialTerminalPivot
import Atlas.LinearGroups.ReeF4.SpecialMarkedLine
import Atlas.LinearGroups.ReeF4.SpecialPoints

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Actual normalized vectors in one intrinsic leading-root stratum.
Normalization is projective, not an extra group or incidence assumption. -/
def NormalizedSpecialChart (m : ℕ) (r : Fin 26) :=
  {u : TraceZero F // IsSpecialVector m u ∧ isotropyCoordinates u r=1 ∧
    ∀ j, specialAbsoluteGrade r<specialAbsoluteGrade j → isotropyCoordinates u j=0}

private theorem lowestRoot_above_zero :
    ∀ j, specialAbsoluteGrade 2<specialAbsoluteGrade j →
      isotropyCoordinates (rootVector (F := F) (0,0)) j=0 := by
  intro j hj
  change (-12 : ℤ) < specialAbsoluteGrade j at hj
  fin_cases j <;> norm_num [specialAbsoluteGrade,Matrix.cons_val] at hj
  all_goals simp [isotropyCoordinates,rootVector,Pi.single_apply]

def lowestChartPoint (m : ℕ) : NormalizedSpecialChart (F := F) m 2 :=
  ⟨rootVector (0,0),isSpecialVector_firstRoot m,
    by simp [isotropyCoordinates,rootVector],lowestRoot_above_zero⟩

theorem normalizedChart2_eq_root (m : ℕ) (u : NormalizedSpecialChart (F := F) m 2) :
    u.val=rootVector (0,0) := by
  have ha : u.val.val.2 0 0=1 := u.property.2.1
  have hc : u.val.val.2 2 0=0 := u.property.2.2 18 (by decide)
  have hz : ∀ j, specialAbsoluteGrade 18<specialAbsoluteGrade j → isotropyCoordinates u.val j=0 := by
    intro j hj
    exact u.property.2.2 j (lt_trans (by decide : specialAbsoluteGrade 2<specialAbsoluteGrade 18) hj)
  simpa only [ha,hc,one_smul,zero_smul,add_zero] using terminal_support hz

def normalizedChart2Equiv (m : ℕ) : NormalizedSpecialChart (F := F) m 2 ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := lowestChartPoint m
  left_inv u := Subtype.ext (normalizedChart2_eq_root m u).symm
  right_inv u := by cases u; rfl

private theorem nextRoot_sum_above_zero (a : F) :
    ∀ j, specialAbsoluteGrade 18<specialAbsoluteGrade j →
      isotropyCoordinates (a • rootVector (F := F) (0,0)+rootVector (2,0)) j=0 := by
  intro j hj
  change (-11 : ℤ) < specialAbsoluteGrade j at hj
  fin_cases j <;> norm_num [specialAbsoluteGrade,Matrix.cons_val] at hj
  all_goals simp [isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

def nextChartPoint {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) :
    NormalizedSpecialChart (F := F) m 18 :=
  ⟨a • rootVector (0,0)+rootVector (2,0),by
    simpa only [one_smul] using isSpecialVector_markedLine_combination hcard a 1 (Or.inr one_ne_zero),
    by simp [isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul],nextRoot_sum_above_zero a⟩

theorem normalizedChart18_eq_sum {m : ℕ} (u : NormalizedSpecialChart (F := F) m 18) :
    u.val=(u.val.val.2 0 0) • rootVector (0,0)+rootVector (2,0) := by
  have hc : u.val.val.2 2 0=1 := u.property.2.1
  simpa only [hc,one_smul] using terminal_support u.property.2.2

def normalizedChart18Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 18 ≃ F where
  toFun u := u.val.val.2 0 0
  invFun := nextChartPoint hcard
  left_inv u := Subtype.ext (normalizedChart18_eq_sum u).symm
  right_inv a := by simp [nextChartPoint,rootVector,Pi.single_apply,smul_eq_mul]

theorem card_normalizedChart2 (m : ℕ) : Nat.card (NormalizedSpecialChart (F := F) m 2)=1 := by
  rw [Nat.card_congr (normalizedChart2Equiv m)]
  simp

theorem card_normalizedChart18 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 18)=Nat.card F :=
  Nat.card_congr (normalizedChart18Equiv hcard)
end Atlas.ReeF4
