import Atlas.LinearGroups.ReeF4.SpecialAdjointTopData

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem specialAdjoint9_quartic_identity (x y : Fin 26 → F) :
    specialAdjoint9 (isotropyRawStar x y) = specialAdjoint9Certificate x y := by
  simp only [specialAdjoint9, isotropyRawStar, specialAdjoint9Certificate,
    isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
end Atlas.ReeF4
