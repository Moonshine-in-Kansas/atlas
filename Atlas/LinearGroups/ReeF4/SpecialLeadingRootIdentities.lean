import Atlas.LinearGroups.ReeF4.SpecialAdjoint
import Atlas.LinearGroups.ReeF4.SpecialSecondPivotVanishing

/-! UNCOMPILED discovery identities. No witness normalization assumed. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem leading8_raw_identity (x y : Fin 26 → F)
    (h9 : x 9 = 0) (h15 : x 15 = 0) (h16 : x 16 = 0) (h17 : x 17 = 0) (h24 : x 24 = 0) (h25 : x 25 = 0) :
    x 8 ^ 1 * isotropyRawStar x y 8 =
    (y 15) * fullAdjointRoot24 x +
    (y 21) * specialAdjoint17 x +
    (y 23) * fullAdjointRoot16 x +
    (x 3) * isotropyRawStar x y 9 := by
  simp only [isotropyRawStar, isotropyCross, isotropyPolar, fullAdjointRoot24, specialAdjoint17, fullAdjointRoot16,
    Matrix.cons_val, h9, h15, h16, h17, h24, h25, mul_zero, zero_mul, add_zero, zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod, CharTwo.two_eq_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem leading23_raw_identity (x y : Fin 26 → F)
    (h8 : x 8 = 0) (h9 : x 9 = 0) (h15 : x 15 = 0) (h16 : x 16 = 0) (h17 : x 17 = 0) (h24 : x 24 = 0) (h25 : x 25 = 0) :
    x 23 ^ 2 * isotropyRawStar x y 23 =
    (x 0 * y 17) * fullAdjointRoot15 x +
    (x 7 * y 25) * fullAdjointRoot14 x +
    (x 21 * y 17) * fullAdjointRoot7 x +
    (x 14 * y 25) * fullAdjointRoot7 x +
    (x 23 * y 17) * fullAdjointRoot6 x +
    (x 20 * x 23) * isotropyRawStar x y 25 +
    (x 5 * x 6) * isotropyRawStar x y 25 +
    (x 1 * x 1) * isotropyRawStar x y 25 +
    (x 0 * x 1) * isotropyRawStar x y 25 +
    (x 22 * x 23) * isotropyRawStar x y 17 +
    (x 5 * x 7) * isotropyRawStar x y 17 +
    (x 21 * x 23) * isotropyRawStar x y 15 +
    (x 1 * x 23) * isotropyCross x y 25 +
    (x 6 * x 23) * isotropyCross x y 17 +
    (x 7 * x 23) * isotropyCross x y 16 +
    (x 13 * x 23) * isotropyCross x y 9 +
    (x 1 * x 7) * isotropyCross x y 9 +
    (x 0 * x 7) * isotropyCross x y 9 := by
  simp only [isotropyRawStar, isotropyCross, isotropyPolar, fullAdjointRoot15, fullAdjointRoot14, fullAdjointRoot7, fullAdjointRoot6,
    Matrix.cons_val, h8, h9, h15, h16, h17, h24, h25, mul_zero, zero_mul, add_zero, zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod, CharTwo.two_eq_zero]

end Atlas.ReeF4
