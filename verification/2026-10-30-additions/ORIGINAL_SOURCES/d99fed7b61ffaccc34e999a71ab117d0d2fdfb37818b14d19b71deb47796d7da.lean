import F4Work.TailRhoData

/-!
Source-only fixed-index branch of the preserved TailRhoAction proof.
This module contains one operator identity on the same 27 carrier coordinates.
No Lean/checker run or memory improvement is claimed.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem tailRhoCarrier_long_0 (m : ℕ) (u : F) (w : Carrier F) :
    tailRhoCarrier (alternatingLongFormula m (0 : Fin 4) u w) =
      alternatingLongFormula m (Fin.rev (0 : Fin 4)) u (tailRhoCarrier w) := by
  change tailRhoCarrier (alternatingLongFormula m 0 u w) =
    alternatingLongFormula m 3 u (tailRhoCarrier w)
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp only [Fin.reduceFinMk, Matrix.cons_val, tailRhoCarrier,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.head_cons,
        ree_f4_factor_rows] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.reduceFinMk, Matrix.cons_val, tailRhoCarrier,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.head_cons,
        ree_f4_factor_rows] <;> ring

end Atlas.ReeF4
