import Atlas.LinearGroups.Orthogonal.Elementary
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Mathlib.Tactic

/-! Literal split orthogonal root transformations, in every characteristic. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {K : Type*} [Field K] {n : ℕ}

private theorem perpendicular_ef (i j : Fin n) (h : i ≠ j) (t : K) :
    (formD n K).polarBilin (e i) (t • f j) = 0 := by
  simp [-QuadraticMap.polarBilin_apply_apply, e, Pi.single_apply, h, Ne.symm h]

private theorem perpendicular_ee (i j : Fin n) (t : K) :
    (formD n K).polarBilin (e i) (t • e j) = 0 := by
  rw [map_smul, polarD_e]
  simp [e, Pi.single_apply]

/-- The root e_i-e_j: I+tE_{i,j}-tE_{-j,-i}. -/
def differenceRoot (i j : Fin n) (h : i ≠ j) (t : K) : O_DPlus n K :=
  siegelElement (formD n K) (e i) (t • f j) (formD_e i) (perpendicular_ef i j h t)

/-- The root e_i+e_j: I+tE_{i,-j}-tE_{j,-i}. -/
def sumRoot (i j : Fin n) (t : K) : O_DPlus n K :=
  siegelElement (formD n K) (e i) (t • e j) (formD_e i) (perpendicular_ee i j t)

theorem differenceRoot_mem (i j : Fin n) (h : i ≠ j) (t : K) :
    differenceRoot i j h t ∈ elementarySubgroup (formD n K) :=
  siegelElement_mem _ _ _ _ _

theorem sumRoot_mem (i j : Fin n) (t : K) :
    sumRoot i j t ∈ elementarySubgroup (formD n K) :=
  siegelElement_mem _ _ _ _ _

theorem differenceRoot_apply (i j : Fin n) (h : i ≠ j) (t : K) (x : VectorD n K) :
    (differenceRoot i j h t).val x =
      x + (t * x (.inl j)) • e i - (t * x (.inr i)) • f j := by
  change Atlas.Quadratic.siegel (formD n K) (e i) (t • f j) x = _
  simp only [Atlas.Quadratic.siegel, QuadraticMap.map_smul, map_smul, polarD_e, polarD_f, formD_e, formD_f, mul_zero, zero_mul, zero_smul, sub_zero, smul_smul, smul_eq_mul]
  simp only [mul_comm]

theorem sumRoot_apply (i j : Fin n) (t : K) (x : VectorD n K) :
    (sumRoot i j t).val x =
      x + (t * x (.inr j)) • e i - (t * x (.inr i)) • e j := by
  change Atlas.Quadratic.siegel (formD n K) (e i) (t • e j) x = _
  simp only [Atlas.Quadratic.siegel, QuadraticMap.map_smul, map_smul, polarD_e, polarD_f, formD_e, formD_f, mul_zero, zero_mul, zero_smul, sub_zero, smul_smul, smul_eq_mul]
  simp only [mul_comm]


/-- The transpose root opposite to e_i+e_j. -/
def negativeSumRoot (i j : Fin n) (t : K) : O_DPlus n K :=
  siegelElement (formD n K) (f j) (t • f i) (formD_f j) (by
    rw [map_smul, polarD_f]
    simp [f])

theorem negativeSumRoot_mem (i j : Fin n) (t : K) :
    negativeSumRoot i j t ∈ elementarySubgroup (formD n K) :=
  siegelElement_mem _ _ _ _ _

theorem negativeSumRoot_apply (i j : Fin n) (t : K) (x : VectorD n K) :
    (negativeSumRoot i j t).val x =
      x + (t * x (.inl i)) • f j - (t * x (.inl j)) • f i := by
  change Atlas.Quadratic.siegel (formD n K) (f j) (t • f i) x = _
  simp only [Atlas.Quadratic.siegel, QuadraticMap.map_smul, map_smul, polarD_f,
    formD_f, mul_zero, zero_mul, zero_smul, sub_zero, smul_smul, smul_eq_mul]
  simp only [mul_comm]

theorem differenceRoot_add (i j : Fin n) (h : i ≠ j) (s t : K) :
    differenceRoot i j h (s+t) = differenceRoot i j h s * differenceRoot i j h t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Atlas.Quadratic.siegel _ _ ((s+t) • f j) x =
    Atlas.Quadratic.siegel _ _ (s • f j) (Atlas.Quadratic.siegel _ _ (t • f j) x)
  rw [Atlas.Quadratic.siegel_add _ _ _ _ _ (formD_e i)
    (perpendicular_ef i j h s) (perpendicular_ef i j h t), add_smul]

theorem sumRoot_add (i j : Fin n) (s t : K) :
    sumRoot i j (s+t) = sumRoot i j s * sumRoot i j t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Atlas.Quadratic.siegel _ _ ((s+t) • e j) x =
    Atlas.Quadratic.siegel _ _ (s • e j) (Atlas.Quadratic.siegel _ _ (t • e j) x)
  rw [Atlas.Quadratic.siegel_add _ _ _ _ _ (formD_e i)
    (perpendicular_ee i j s) (perpendicular_ee i j t), add_smul]

/-- The fixed pinning (e1-e2,e2-e3,e3-e4,e3+e4). -/
def pinnedRoot (i : Fin 4) (t : K) : O_DPlus 4 K :=
  ![differenceRoot 0 1 (by decide) t, differenceRoot 1 2 (by decide) t,
    differenceRoot 2 3 (by decide) t, sumRoot 2 3 t] i

def pinnedNegativeRoot (i : Fin 4) (t : K) : O_DPlus 4 K :=
  ![differenceRoot 1 0 (by decide) t, differenceRoot 2 1 (by decide) t,
    differenceRoot 3 2 (by decide) t, negativeSumRoot 2 3 t] i

theorem pinnedRoot_mem (i : Fin 4) (t : K) :
    pinnedRoot i t ∈ elementarySubgroup (formD 4 K) := by
  fin_cases i
  · exact differenceRoot_mem 0 1 (by decide) t
  · exact differenceRoot_mem 1 2 (by decide) t
  · exact differenceRoot_mem 2 3 (by decide) t
  · exact sumRoot_mem 2 3 t

theorem pinnedNegativeRoot_mem (i : Fin 4) (t : K) :
    pinnedNegativeRoot i t ∈ elementarySubgroup (formD 4 K) := by
  fin_cases i
  · exact differenceRoot_mem 1 0 (by decide) t
  · exact differenceRoot_mem 2 1 (by decide) t
  · exact differenceRoot_mem 3 2 (by decide) t
  · exact negativeSumRoot_mem 2 3 t

end Atlas.Triality
