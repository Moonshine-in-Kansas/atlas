import Atlas.LinearGroups.ReeF4.AlternatingRootWordCoordinates
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192
theorem alternatingShort_row_2_0 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).1 0 =
      ((w.1 0)) := by rfl
theorem alternatingShort_row_2_1 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).1 1 =
      ((w.1 1) + b*(w.2 0 7)) + a*((w.2 0 6)) + a*(theta F m a)*((w.2 0 7)) := by rfl
theorem alternatingShort_row_2_2 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).1 2 =
      ((w.1 2) + b*(w.2 0 7)) + a*((w.2 0 6)) + a*(theta F m a)*((w.2 0 7)) := by rfl
theorem alternatingShort_row_2_3 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 0 =
      ((w.2 0 0) + b*((w.1 1)+(w.1 2)) + (theta F m b)*(w.2 0 6) + b^2*(w.2 0 7)) + (theta F m a)*((w.2 0 1) + (theta F m b)*(w.2 0 7)) + a^2*(theta F m a)*((w.2 0 6)) + a^2*((theta F m a))^2*((w.2 0 7)) := by rfl
theorem alternatingShort_row_2_4 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 1 =
      ((w.2 0 1) + (theta F m b)*(w.2 0 7)) + a*(((w.1 1) + b*(w.2 0 7))+((w.1 2) + b*(w.2 0 7))) + a^2*((w.2 0 6)) := by rfl
theorem alternatingShort_row_2_5 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 2 =
      ((w.2 0 2)) := by rfl
theorem alternatingShort_row_2_6 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 3 =
      ((w.2 0 3)) := by rfl
theorem alternatingShort_row_2_7 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 4 =
      ((w.2 0 4)) := by rfl
theorem alternatingShort_row_2_8 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 5 =
      ((w.2 0 5)) := by rfl
theorem alternatingShort_row_2_9 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 6 =
      ((w.2 0 6)) + (theta F m a)*((w.2 0 7)) := by rfl
theorem alternatingShort_row_2_10 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 0 7 =
      ((w.2 0 7)) := by rfl
theorem alternatingShort_row_2_11 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 0 =
      ((w.2 1 0) + (theta F m b)*(w.2 1 6) + b*(w.2 2 3)) + a^2*(theta F m a)*((w.2 1 6)) + a*((w.2 2 2) + b*(w.2 1 6)) + a*(theta F m a)*((w.2 2 3)) := by rfl
theorem alternatingShort_row_2_12 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 1 =
      ((w.2 1 1) + (theta F m b)*(w.2 1 7) + b*(w.2 2 5)) + a^2*(theta F m a)*((w.2 1 7)) + a*((w.2 2 4) + b*(w.2 1 7)) + a*(theta F m a)*((w.2 2 5)) := by rfl
theorem alternatingShort_row_2_13 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 2 =
      ((w.2 1 2) + b*(w.2 2 6)) + (theta F m a)*((w.2 1 4)) := by rfl
theorem alternatingShort_row_2_14 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 3 =
      ((w.2 1 3) + b*(w.2 2 7)) + (theta F m a)*((w.2 1 5)) := by rfl
theorem alternatingShort_row_2_15 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 4 =
      ((w.2 1 4)) + a*((w.2 2 6)) := by rfl
theorem alternatingShort_row_2_16 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 5 =
      ((w.2 1 5)) + a*((w.2 2 7)) := by rfl
theorem alternatingShort_row_2_17 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 6 =
      ((w.2 1 6)) := by rfl
theorem alternatingShort_row_2_18 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 1 7 =
      ((w.2 1 7)) := by rfl
theorem alternatingShort_row_2_19 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 0 =
      ((w.2 2 0) + b*(w.2 1 4) + (theta F m b)*(w.2 2 6)) + a*((w.2 1 2) + b*(w.2 2 6)) + a*(theta F m a)*((w.2 1 4)) + a^2*(theta F m a)*((w.2 2 6)) := by rfl
theorem alternatingShort_row_2_20 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 1 =
      ((w.2 2 1) + b*(w.2 1 5) + (theta F m b)*(w.2 2 7)) + a*((w.2 1 3) + b*(w.2 2 7)) + a*(theta F m a)*((w.2 1 5)) + a^2*(theta F m a)*((w.2 2 7)) := by rfl
theorem alternatingShort_row_2_21 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 2 =
      ((w.2 2 2) + b*(w.2 1 6)) + (theta F m a)*((w.2 2 3)) := by rfl
theorem alternatingShort_row_2_22 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 3 =
      ((w.2 2 3)) + a*((w.2 1 6)) := by rfl
theorem alternatingShort_row_2_23 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 4 =
      ((w.2 2 4) + b*(w.2 1 7)) + (theta F m a)*((w.2 2 5)) := by rfl
theorem alternatingShort_row_2_24 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 5 =
      ((w.2 2 5)) + a*((w.2 1 7)) := by rfl
theorem alternatingShort_row_2_25 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 6 =
      ((w.2 2 6)) := by rfl
theorem alternatingShort_row_2_26 (m : ℕ) (a b : F) (w : Carrier F) :
    (alternatingShortFormula m 2 a b w).2 2 7 =
      ((w.2 2 7)) := by rfl
end Atlas.ReeF4
