import Atlas.LinearGroups.ReeF4.LongRootInvolution

/-! Direct coordinates for the source long-root operator, for polynomial checking. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def longRootFormula (w : Carrier F) : Carrier F :=
  (![w.1 0 + w.2 1 4, w.1 1, w.1 2 + w.2 1 4],
   ![![w.2 0 0 + w.2 2 0, w.2 0 1 + w.2 0 2, w.2 0 2, w.2 0 3,
        w.2 0 4 + w.2 2 3, w.2 0 5 + w.2 0 6 + w.2 2 5 + w.2 2 6,
        w.2 0 6 + w.2 2 6, w.2 0 7],
     ![w.2 1 0, w.2 1 1 + w.2 1 2, w.2 1 2, w.2 1 3 + w.1 0 + w.1 2 + w.2 1 4,
        w.2 1 4, w.2 1 5 + w.2 1 6, w.2 1 6, w.2 1 7],
     ![w.2 2 0, w.2 2 1 + w.2 0 1 + w.2 0 2 + w.2 2 2, w.2 2 2 + w.2 0 2,
        w.2 2 3, w.2 2 4 + w.2 0 3, w.2 2 5 + w.2 2 6, w.2 2 6,
        w.2 2 7 + w.2 0 7]])

theorem longRootFormula_trace (w : Carrier F) : trace (longRootFormula w) = trace w := by
  simp [longRootFormula, trace]
  linear_combination w.2 1 4 * (CharTwo.two_eq_zero (R := F))

def longRootCoordinateLinear : TraceZero F →ₗ[F] TraceZero F where
  toFun w := ⟨longRootFormula w.val, by
    change trace (longRootFormula w.val) = 0
    rw [longRootFormula_trace]
    exact w.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [longRootFormula] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [longRootFormula] <;> ring
  map_smul' a u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [longRootFormula, smul_eq_mul] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [longRootFormula, smul_eq_mul] <;> ring

theorem longRootFormula_unit : longRootFormula (unit : Carrier F) = unit := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [longRootFormula, unit, CharTwo.add_self_eq_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [longRootFormula, unit, CharTwo.add_self_eq_zero]

end Atlas.ReeF4
