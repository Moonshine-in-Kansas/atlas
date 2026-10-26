import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row24

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot24 (x : Fin 26 → F) : F := x 0*x 24 + x 1*x 24 + x 4*x 17 + x 5*x 16 + x 8*x 14 + x 9*x 12
def fullAdjointRoot24Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 14*y 16 + x 16*y 14 + x 21*y 24 + x 24*y 21) + (isotropyCross x y 1) * (x 14*y 16 + x 16*y 14) + (isotropyCross x y 3) * (x 16*y 24 + x 24*y 16) + (isotropyCross x y 4) * (x 0*y 9 + x 9*y 0 + x 14*y 25 + x 16*y 23 + x 23*y 16 + x 25*y 14) + (isotropyCross x y 5) * (x 16*y 21 + x 21*y 16) + (isotropyCross x y 6) * (x 14*y 24 + x 24*y 14) + (isotropyCross x y 8) * (x 14*y 21 + x 21*y 14) + (isotropyCross x y 9) * (x 0*y 4 + x 4*y 0 + x 14*y 20 + x 16*y 18 + x 18*y 16 + x 20*y 14) + (isotropyCross x y 10) * (x 9*y 24 + x 24*y 9) + (isotropyCross x y 12) * (x 9*y 21 + x 21*y 9) + (isotropyCross x y 14) * (x 1*y 16 + x 4*y 25 + x 9*y 20 + x 16*y 1 + x 20*y 9 + x 25*y 4) + (isotropyCross x y 15) * (x 4*y 24 + x 24*y 4) + (isotropyCross x y 16) * (x 1*y 14 + x 4*y 23 + x 9*y 18 + x 14*y 1 + x 18*y 9 + x 23*y 4) + (isotropyCross x y 17) * (x 4*y 21 + x 21*y 4) + (isotropyCross x y 18) * (x 9*y 16 + x 16*y 9) + (isotropyCross x y 20) * (x 9*y 14 + x 14*y 9) + (isotropyCross x y 21) * (x 0*y 24 + x 5*y 16 + x 8*y 14 + x 14*y 8 + x 16*y 5 + x 24*y 0) + (isotropyCross x y 23) * (x 4*y 16 + x 16*y 4) + (isotropyCross x y 24) * (x 0*y 21 + x 3*y 16 + x 6*y 14 + x 14*y 6 + x 16*y 3 + x 21*y 0) + (isotropyCross x y 25) * (x 4*y 14 + x 14*y 4)

theorem fullAdjointRoot24_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 6 = fullAdjointRoot24 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot24,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot24_actual (u : TraceZero F) :
    (adjoint u.val).2 2 6 = fullAdjointRoot24 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot24_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot24_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot24 (isotropyRawStar x y) = fullAdjointRoot24Certificate x y := by
  simp only [fullAdjointRoot24, isotropyRawStar, fullAdjointRoot24Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root24_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 6 = 0 := by
  rw [fullAdjointRoot24_actual,isotropyRawStar_actual,fullAdjointRoot24_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot24Certificate,hc,hp]
end Atlas.ReeF4
