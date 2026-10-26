import Atlas.LinearGroups.ReeF4.AlternatingRootWordCoordinates
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192
theorem alternatingLong_row_2_0 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).1 0 =
      (w.1 0) + u*(w.2 1 6) := by rfl
theorem alternatingLong_row_2_1 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).1 1 =
      (w.1 1) := by rfl
theorem alternatingLong_row_2_2 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).1 2 =
      (w.1 2) + u*(w.2 1 6) := by rfl
theorem alternatingLong_row_2_3 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 0 =
      (w.2 0 0) + (theta F m u)*(w.2 0 3) + u*(w.2 2 2) + u*(theta F m u)*(w.2 2 6) := by rfl
theorem alternatingLong_row_2_4 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 1 =
      (w.2 0 1) + u*(w.2 2 3) := by rfl
theorem alternatingLong_row_2_5 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 2 =
      (w.2 0 2) := by rfl
theorem alternatingLong_row_2_6 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 3 =
      (w.2 0 3) + u*(w.2 2 6) := by rfl
theorem alternatingLong_row_2_7 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 4 =
      (w.2 0 4) + (theta F m u)*(w.2 0 7) := by rfl
theorem alternatingLong_row_2_8 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 5 =
      (w.2 0 5) + u*(w.2 2 7) := by rfl
theorem alternatingLong_row_2_9 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 6 =
      (w.2 0 6) := by rfl
theorem alternatingLong_row_2_10 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 0 7 =
      (w.2 0 7) := by rfl
theorem alternatingLong_row_2_11 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 0 =
      (w.2 1 0) + (theta F m u)*(w.2 1 4) := by rfl
theorem alternatingLong_row_2_12 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 1 =
      (w.2 1 1) + u*((w.1 0)+(w.1 2)) + u^2*(w.2 1 6) := by rfl
theorem alternatingLong_row_2_13 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 2 =
      (w.2 1 2) := by rfl
theorem alternatingLong_row_2_14 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 3 =
      (w.2 1 3) + (theta F m u)*(w.2 1 7) := by rfl
theorem alternatingLong_row_2_15 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 4 =
      (w.2 1 4) := by rfl
theorem alternatingLong_row_2_16 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 5 =
      (w.2 1 5) := by rfl
theorem alternatingLong_row_2_17 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 6 =
      (w.2 1 6) := by rfl
theorem alternatingLong_row_2_18 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 1 7 =
      (w.2 1 7) := by rfl
theorem alternatingLong_row_2_19 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 0 =
      (w.2 2 0) + u*(w.2 0 2) := by rfl
theorem alternatingLong_row_2_20 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 1 =
      (w.2 2 1) + u*(w.2 0 4) + u*(theta F m u)*(w.2 0 7) + (theta F m u)*(w.2 2 5) := by rfl
theorem alternatingLong_row_2_21 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 2 =
      (w.2 2 2) + (theta F m u)*(w.2 2 6) := by rfl
theorem alternatingLong_row_2_22 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 3 =
      (w.2 2 3) := by rfl
theorem alternatingLong_row_2_23 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 4 =
      (w.2 2 4) + u*(w.2 0 6) := by rfl
theorem alternatingLong_row_2_24 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 5 =
      (w.2 2 5) + u*(w.2 0 7) := by rfl
theorem alternatingLong_row_2_25 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 6 =
      (w.2 2 6) := by rfl
theorem alternatingLong_row_2_26 (m : ℕ) (u : F) (w : Carrier F) :
    (alternatingLongFormula m 2 u w).2 2 7 =
      (w.2 2 7) := by rfl
end Atlas.ReeF4
