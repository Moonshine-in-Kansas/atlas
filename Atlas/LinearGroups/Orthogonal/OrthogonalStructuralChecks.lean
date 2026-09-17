import Atlas.LinearGroups.Orthogonal.DStructureAllChar
import Atlas.LinearGroups.Orthogonal.Radical
import Atlas.LinearGroups.Orthogonal.Transitivity
import Atlas.LinearGroups.Orthogonal.FullDicksonD

/-! # Radical, center and intrinsic Dickson boundary regressions -/
namespace Atlas.Orthogonal.Checks

theorem d4_three_center_order :
    Nat.card (Subgroup.center (elementarySubgroup (formD 4 (ZMod 3)))) = 2 := by
  have h := card_elementaryD_center_all_char_mul_gcd_two (F := ZMod 3) 1
  norm_num [Nat.card_zmod] at h
  change Nat.card (Subgroup.center (elementarySubgroup (formD 4 (ZMod 3)))) * 2 = 4 at h
  omega

theorem b3_two_polar_radical (v : VectorB 3 (ZMod 2)) :
    (∀ w, (formB 3 (ZMod 2)).polarBilin v w = 0) ↔
      ∃ a : ZMod 2, v = a • (z (n := 3)) :=
  polarB_radical_charTwo (by decide) v

theorem b3_two_radical_vector_norm : formB 3 (ZMod 2) (z (n := 3)) = 1 := formB_z

theorem b3_two_quadratic_radical : (formB 3 (ZMod 2)).radical = ⊥ := radicalB_eq_bot

theorem d4_two_dickson_exchange :
    fullDicksonD (F := ZMod 2) 1 (splitDExchangeElement (0 : Fin 4)) =
      Multiplicative.ofAdd 1 := fullDicksonD_exchange 1 0

theorem d4_two_dickson_surjective :
    Function.Surjective (fullDicksonD (F := ZMod 2) 1) := fullDicksonD_surjective 1

theorem d4_two_dickson_kernel : (fullDicksonD (F := ZMod 2) 1).ker =
    elementarySubgroup (formD 4 (ZMod 2)) := fullDicksonD_kernel_elementary 1
end Atlas.Orthogonal.Checks
