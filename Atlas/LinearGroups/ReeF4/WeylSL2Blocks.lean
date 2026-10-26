import Atlas.LinearGroups.ReeF4.WeylSL2Parameters

/-! Explicit block coordinates for the actual trace-zero Albert module. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

abbrev LongSL2Blocks (F : Type*) :=
  (Fin 4 → Fin 2 → F) × (Fin 2 → Fin 2 → F) ×
    (Fin 2 → Fin 2 → Fin 2 → F) × (Fin 2 → Fin 2 → F) × (Fin 2 → F)

def longSL2ToBlocks (w : TraceZero F) : LongSL2Blocks F :=
  (![![w.val.2 2 7, w.val.2 0 7], ![w.val.2 0 0, w.val.2 2 0],
      ![w.val.2 0 4, w.val.2 2 3], ![w.val.2 2 4, w.val.2 0 3]],
   ![![w.val.2 1 5, w.val.2 1 6], ![w.val.2 1 1, w.val.2 1 2]],
   ![![![w.val.2 2 1, w.val.2 2 2], ![w.val.2 0 1, w.val.2 0 2]],
     ![![w.val.2 0 5, w.val.2 0 6], ![w.val.2 2 5, w.val.2 2 6]]],
   ![![w.val.2 1 3, w.val.1 0], ![w.val.1 2, w.val.2 1 4]],
   ![w.val.2 1 0, w.val.2 1 7])

def longSL2FromBlocksFormula (b : LongSL2Blocks F) : Carrier F :=
  (![b.2.2.2.1 0 1, b.2.2.2.1 1 0 + b.2.2.2.1 0 1, b.2.2.2.1 1 0],
   ![![b.1 1 0, b.2.2.1 0 1 0, b.2.2.1 0 1 1, b.1 3 1,
        b.1 2 0, b.2.2.1 1 0 0, b.2.2.1 1 0 1, b.1 0 1],
     ![b.2.2.2.2 0, b.2.1 1 0, b.2.1 1 1, b.2.2.2.1 0 0,
        b.2.2.2.1 1 1, b.2.1 0 0, b.2.1 0 1, b.2.2.2.2 1],
     ![b.1 1 1, b.2.2.1 0 0 0, b.2.2.1 0 0 1, b.1 2 1,
        b.1 3 0, b.2.2.1 1 1 0, b.2.2.1 1 1 1, b.1 0 0]])

theorem longSL2FromBlocksFormula_trace (b : LongSL2Blocks F) :
    trace (longSL2FromBlocksFormula b) = 0 := by
  simp [longSL2FromBlocksFormula, trace]
  linear_combination
    (b.2.2.2.1 0 1 + b.2.2.2.1 1 0) * (CharTwo.two_eq_zero (R := F))

def longSL2FromBlocks (b : LongSL2Blocks F) : TraceZero F :=
  ⟨longSL2FromBlocksFormula b, longSL2FromBlocksFormula_trace b⟩

theorem longSL2FromBlocks_toBlocks (w : TraceZero F) :
    longSL2FromBlocks (longSL2ToBlocks w) = w := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i
    · rfl
    · change w.val.1 2 + w.val.1 0 = w.val.1 1
      have hw : w.val.1 0 + w.val.1 1 + w.val.1 2 = 0 := w.property
      linear_combination hw - w.val.1 1 * (CharTwo.two_eq_zero (R := F))
    · rfl
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem longSL2ToBlocks_fromBlocks (b : LongSL2Blocks F) :
    longSL2ToBlocks (longSL2FromBlocks b) = b := by
  apply Prod.ext
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · apply Prod.ext
    · funext i j; fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · funext i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl
      · apply Prod.ext
        · funext i j; fin_cases i <;> fin_cases j <;> rfl
        · funext i; fin_cases i <;> rfl

def longSL2BlocksEquiv : TraceZero F ≃ₗ[F] LongSL2Blocks F where
  toFun := longSL2ToBlocks
  invFun := longSL2FromBlocks
  left_inv := longSL2FromBlocks_toBlocks
  right_inv := longSL2ToBlocks_fromBlocks
  map_add' u v := by
    apply Prod.ext
    · funext i j; fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · funext i j; fin_cases i <;> fin_cases j <;> rfl
      · apply Prod.ext
        · funext i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl
        · apply Prod.ext
          · funext i j; fin_cases i <;> fin_cases j <;> rfl
          · funext i; fin_cases i <;> rfl
  map_smul' a u := by
    apply Prod.ext
    · funext i j; fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · funext i j; fin_cases i <;> fin_cases j <;> rfl
      · apply Prod.ext
        · funext i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl
        · apply Prod.ext
          · funext i j; fin_cases i <;> fin_cases j <;> rfl
          · funext i; fin_cases i <;> rfl

end Atlas.ReeF4
