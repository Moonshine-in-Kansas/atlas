import Atlas.LinearGroups.ReeF4.ShortRootOperator

/-! Direct Albert coordinates of Wilson's order-four short-root operator.
The extension to the 27-space fixes the Albert unit; its restriction is the
source operator on the 26-dimensional trace kernel. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def shortRootFormula (w : Carrier F) : Carrier F :=
  (![w.1 0, w.1 1 + w.2 0 4 + w.2 0 5, w.1 2 + w.2 0 4 + w.2 0 5],
   ![![w.2 0 0, w.2 0 1, w.2 0 2 + w.2 0 3 + w.2 0 4 + w.2 0 5,
        w.2 0 3 + w.1 1 + w.1 2 + w.2 0 4, w.2 0 4 + w.2 0 5,
        w.2 0 5, w.2 0 6, w.2 0 7],
     ![w.2 1 0 + w.2 1 1, w.2 1 1 + w.2 2 1,
        w.2 1 2 + w.2 1 3 + w.2 2 2 + w.2 2 4, w.2 1 3,
        w.2 1 4 + w.2 1 5 + w.2 2 3 + w.2 2 5, w.2 1 5,
        w.2 1 6 + w.2 1 7, w.2 1 7 + w.2 2 7],
     ![w.2 2 0 + w.2 1 0 + w.2 1 1 + w.2 2 1, w.2 2 1,
        w.2 2 2 + w.2 2 4, w.2 2 3 + w.2 2 5, w.2 2 4 + w.2 1 3,
        w.2 2 5 + w.2 1 5, w.2 2 6 + w.2 1 6 + w.2 1 7 + w.2 2 7,
        w.2 2 7]])

theorem shortRootFormula_trace (w : Carrier F) : trace (shortRootFormula w) = trace w := by
  simp [shortRootFormula, trace]
  linear_combination (w.2 0 4 + w.2 0 5) * (CharTwo.two_eq_zero (R := F))

def shortRootCoordinateLinear : TraceZero F →ₗ[F] TraceZero F where
  toFun w := ⟨shortRootFormula w.val, by
    change trace (shortRootFormula w.val) = 0
    rw [shortRootFormula_trace]
    exact w.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [shortRootFormula] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [shortRootFormula] <;> ring
  map_smul' a u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [shortRootFormula, smul_eq_mul] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [shortRootFormula, smul_eq_mul] <;> ring

theorem shortRootFormula_unit : shortRootFormula (unit : Carrier F) = unit := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shortRootFormula, unit, CharTwo.add_self_eq_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [shortRootFormula, unit, CharTwo.add_self_eq_zero]

end Atlas.ReeF4
