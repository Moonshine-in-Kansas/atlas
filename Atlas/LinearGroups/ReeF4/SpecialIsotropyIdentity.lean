import Atlas.LinearGroups.ReeF4.SpecialIsotropyData
import Atlas.LinearGroups.ReeF4.StarCoefficientChecks

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- The proposed 168-term certificate is checked by polynomial normalization
against the explicit coefficient formulas; no external computation is trusted. -/
theorem isotropy_quartic_identity (x y : Fin 26 → F) :
    isotropyQuadratic (isotropyRawStar x y) = isotropyCertificate x y := by
  unfold isotropyQuadratic isotropyRawStar isotropyCertificate isotropyCross isotropyPolar
  simp only [Matrix.cons_val]
  simp only [CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

end Atlas.ReeF4
