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
theorem tailRhoCarrier_short_1 (m : ℕ) (a b : F) (w : Carrier F) :
    tailRhoCarrier (alternatingShortFormula m (1 : Fin 3).succ a b w) =
      alternatingShortFormula m (Fin.rev (1 : Fin 3)).succ a b (tailRhoCarrier w) := by
  change tailRhoCarrier (alternatingShortFormula m 2 a b w) =
    alternatingShortFormula m 2 a b (tailRhoCarrier w)
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
