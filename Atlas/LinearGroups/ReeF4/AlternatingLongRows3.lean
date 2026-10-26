import Atlas.LinearGroups.ReeF4.AlternatingRootWordCoordinates
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192
theorem alternatingLong_row_3_0 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).1 0 =
      (w.1 0) + u*(w.2 1 4) := by rfl
theorem alternatingLong_row_3_1 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).1 1 =
      (w.1 1) := by rfl
theorem alternatingLong_row_3_2 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).1 2 =
      (w.1 2) + u*(w.2 1 4) := by rfl
theorem alternatingLong_row_3_3 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 0 =
      (w.2 0 0) + u*(w.2 2 0) := by rfl
theorem alternatingLong_row_3_4 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 1 =
      (w.2 0 1) + (theta F m u)*(w.2 0 2) := by rfl
theorem alternatingLong_row_3_5 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 2 =
      (w.2 0 2) := by rfl
theorem alternatingLong_row_3_6 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 3 =
      (w.2 0 3) := by rfl
theorem alternatingLong_row_3_7 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 4 =
      (w.2 0 4) + u*(w.2 2 3) := by rfl
theorem alternatingLong_row_3_8 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 5 =
      (w.2 0 5) + u*(w.2 2 5) + u*(theta F m u)*(w.2 2 6) + (theta F m u)*(w.2 0 6) := by rfl
theorem alternatingLong_row_3_9 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 6 =
      (w.2 0 6) + u*(w.2 2 6) := by rfl
theorem alternatingLong_row_3_10 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 0 7 =
      (w.2 0 7) := by rfl
theorem alternatingLong_row_3_11 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 0 =
      (w.2 1 0) := by rfl
theorem alternatingLong_row_3_12 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 1 =
      (w.2 1 1) + (theta F m u)*(w.2 1 2) := by rfl
theorem alternatingLong_row_3_13 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 2 =
      (w.2 1 2) := by rfl
theorem alternatingLong_row_3_14 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 3 =
      (w.2 1 3) + u*((w.1 2)+(w.1 0)) + u^2*(w.2 1 4) := by rfl
theorem alternatingLong_row_3_15 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 4 =
      (w.2 1 4) := by rfl
theorem alternatingLong_row_3_16 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 5 =
      (w.2 1 5) + (theta F m u)*(w.2 1 6) := by rfl
theorem alternatingLong_row_3_17 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 6 =
      (w.2 1 6) := by rfl
theorem alternatingLong_row_3_18 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 1 7 =
      (w.2 1 7) := by rfl
theorem alternatingLong_row_3_19 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 0 =
      (w.2 2 0) := by rfl
theorem alternatingLong_row_3_20 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 1 =
      (w.2 2 1) + (theta F m u)*(w.2 2 2) + u*(w.2 0 1) + u*(theta F m u)*(w.2 0 2) := by rfl
theorem alternatingLong_row_3_21 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 2 =
      (w.2 2 2) + u*(w.2 0 2) := by rfl
theorem alternatingLong_row_3_22 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 3 =
      (w.2 2 3) := by rfl
theorem alternatingLong_row_3_23 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 4 =
      (w.2 2 4) + u*(w.2 0 3) := by rfl
theorem alternatingLong_row_3_24 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 5 =
      (w.2 2 5) + (theta F m u)*(w.2 2 6) := by rfl
theorem alternatingLong_row_3_25 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 6 =
      (w.2 2 6) := by rfl
theorem alternatingLong_row_3_26 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 3 u w).2 2 7 =
      (w.2 2 7) + u*(w.2 0 7) := by rfl
end Atlas.ReeF4
