import Atlas.LinearGroups.ReeF4.AlternatingShortRows0
import Atlas.LinearGroups.ReeF4.AlternatingLongRows0
import Atlas.LinearGroups.ReeF4.AlternatingShortRows1
import Atlas.LinearGroups.ReeF4.AlternatingLongRows1
import Atlas.LinearGroups.ReeF4.AlternatingShortRows2
import Atlas.LinearGroups.ReeF4.AlternatingLongRows2
import Atlas.LinearGroups.ReeF4.AlternatingShortRows3
import Atlas.LinearGroups.ReeF4.AlternatingLongRows3
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem alternatingRootWord_pivot_u2 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fin 4 → F) (v : Fin 4 → F × F) :
    ((alternatingRootWord hcard u v).val (rootVector (2,7))).val.2 0 5 = u 2 := by
  rw [alternatingRootWord_val]
  simp only [alternatingWordFormula,
    alternatingShort_row_0_0, alternatingShort_row_0_1, alternatingShort_row_0_2, alternatingShort_row_0_3, alternatingShort_row_0_4,
    alternatingShort_row_0_5, alternatingShort_row_0_6, alternatingShort_row_0_7, alternatingShort_row_0_8, alternatingShort_row_0_9,
    alternatingShort_row_0_10, alternatingShort_row_0_11, alternatingShort_row_0_12, alternatingShort_row_0_13, alternatingShort_row_0_14,
    alternatingShort_row_0_15, alternatingShort_row_0_16, alternatingShort_row_0_17, alternatingShort_row_0_18, alternatingShort_row_0_19,
    alternatingShort_row_0_20, alternatingShort_row_0_21, alternatingShort_row_0_22, alternatingShort_row_0_23, alternatingShort_row_0_24,
    alternatingShort_row_0_25, alternatingShort_row_0_26, alternatingLong_row_0_0, alternatingLong_row_0_1, alternatingLong_row_0_2,
    alternatingLong_row_0_3, alternatingLong_row_0_4, alternatingLong_row_0_5, alternatingLong_row_0_6, alternatingLong_row_0_7,
    alternatingLong_row_0_8, alternatingLong_row_0_9, alternatingLong_row_0_10, alternatingLong_row_0_11, alternatingLong_row_0_12,
    alternatingLong_row_0_13, alternatingLong_row_0_14, alternatingLong_row_0_15, alternatingLong_row_0_16, alternatingLong_row_0_17,
    alternatingLong_row_0_18, alternatingLong_row_0_19, alternatingLong_row_0_20, alternatingLong_row_0_21, alternatingLong_row_0_22,
    alternatingLong_row_0_23, alternatingLong_row_0_24, alternatingLong_row_0_25, alternatingLong_row_0_26, alternatingShort_row_1_0,
    alternatingShort_row_1_1, alternatingShort_row_1_2, alternatingShort_row_1_3, alternatingShort_row_1_4, alternatingShort_row_1_5,
    alternatingShort_row_1_6, alternatingShort_row_1_7, alternatingShort_row_1_8, alternatingShort_row_1_9, alternatingShort_row_1_10,
    alternatingShort_row_1_11, alternatingShort_row_1_12, alternatingShort_row_1_13, alternatingShort_row_1_14, alternatingShort_row_1_15,
    alternatingShort_row_1_16, alternatingShort_row_1_17, alternatingShort_row_1_18, alternatingShort_row_1_19, alternatingShort_row_1_20,
    alternatingShort_row_1_21, alternatingShort_row_1_22, alternatingShort_row_1_23, alternatingShort_row_1_24, alternatingShort_row_1_25,
    alternatingShort_row_1_26, alternatingLong_row_1_0, alternatingLong_row_1_1, alternatingLong_row_1_2, alternatingLong_row_1_3,
    alternatingLong_row_1_4, alternatingLong_row_1_5, alternatingLong_row_1_6, alternatingLong_row_1_7, alternatingLong_row_1_8,
    alternatingLong_row_1_9, alternatingLong_row_1_10, alternatingLong_row_1_11, alternatingLong_row_1_12, alternatingLong_row_1_13,
    alternatingLong_row_1_14, alternatingLong_row_1_15, alternatingLong_row_1_16, alternatingLong_row_1_17, alternatingLong_row_1_18,
    alternatingLong_row_1_19, alternatingLong_row_1_20, alternatingLong_row_1_21, alternatingLong_row_1_22, alternatingLong_row_1_23,
    alternatingLong_row_1_24, alternatingLong_row_1_25, alternatingLong_row_1_26, alternatingShort_row_2_0, alternatingShort_row_2_1,
    alternatingShort_row_2_2, alternatingShort_row_2_3, alternatingShort_row_2_4, alternatingShort_row_2_5, alternatingShort_row_2_6,
    alternatingShort_row_2_7, alternatingShort_row_2_8, alternatingShort_row_2_9, alternatingShort_row_2_10, alternatingShort_row_2_11,
    alternatingShort_row_2_12, alternatingShort_row_2_13, alternatingShort_row_2_14, alternatingShort_row_2_15, alternatingShort_row_2_16,
    alternatingShort_row_2_17, alternatingShort_row_2_18, alternatingShort_row_2_19, alternatingShort_row_2_20, alternatingShort_row_2_21,
    alternatingShort_row_2_22, alternatingShort_row_2_23, alternatingShort_row_2_24, alternatingShort_row_2_25, alternatingShort_row_2_26,
    alternatingLong_row_2_0, alternatingLong_row_2_1, alternatingLong_row_2_2, alternatingLong_row_2_3, alternatingLong_row_2_4,
    alternatingLong_row_2_5, alternatingLong_row_2_6, alternatingLong_row_2_7, alternatingLong_row_2_8, alternatingLong_row_2_9,
    alternatingLong_row_2_10, alternatingLong_row_2_11, alternatingLong_row_2_12, alternatingLong_row_2_13, alternatingLong_row_2_14,
    alternatingLong_row_2_15, alternatingLong_row_2_16, alternatingLong_row_2_17, alternatingLong_row_2_18, alternatingLong_row_2_19,
    alternatingLong_row_2_20, alternatingLong_row_2_21, alternatingLong_row_2_22, alternatingLong_row_2_23, alternatingLong_row_2_24,
    alternatingLong_row_2_25, alternatingLong_row_2_26, alternatingShort_row_3_0, alternatingShort_row_3_1, alternatingShort_row_3_2,
    alternatingShort_row_3_3, alternatingShort_row_3_4, alternatingShort_row_3_5, alternatingShort_row_3_6, alternatingShort_row_3_7,
    alternatingShort_row_3_8, alternatingShort_row_3_9, alternatingShort_row_3_10, alternatingShort_row_3_11, alternatingShort_row_3_12,
    alternatingShort_row_3_13, alternatingShort_row_3_14, alternatingShort_row_3_15, alternatingShort_row_3_16, alternatingShort_row_3_17,
    alternatingShort_row_3_18, alternatingShort_row_3_19, alternatingShort_row_3_20, alternatingShort_row_3_21, alternatingShort_row_3_22,
    alternatingShort_row_3_23, alternatingShort_row_3_24, alternatingShort_row_3_25, alternatingShort_row_3_26, alternatingLong_row_3_0,
    alternatingLong_row_3_1, alternatingLong_row_3_2, alternatingLong_row_3_3, alternatingLong_row_3_4, alternatingLong_row_3_5,
    alternatingLong_row_3_6, alternatingLong_row_3_7, alternatingLong_row_3_8, alternatingLong_row_3_9, alternatingLong_row_3_10,
    alternatingLong_row_3_11, alternatingLong_row_3_12, alternatingLong_row_3_13, alternatingLong_row_3_14, alternatingLong_row_3_15,
    alternatingLong_row_3_16, alternatingLong_row_3_17, alternatingLong_row_3_18, alternatingLong_row_3_19, alternatingLong_row_3_20,
    alternatingLong_row_3_21, alternatingLong_row_3_22, alternatingLong_row_3_23, alternatingLong_row_3_24, alternatingLong_row_3_25,
    alternatingLong_row_3_26]
  simp [rootVector, Pi.single_apply]
  <;> ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod, CharTwo.two_eq_zero]
end Atlas.ReeF4
