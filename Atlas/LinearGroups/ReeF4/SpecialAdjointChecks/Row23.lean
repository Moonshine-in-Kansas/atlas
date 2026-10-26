import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row22

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot22 (x : Fin 26 → F) : F := x 0*x 22 + x 1*x 22 + x 2*x 17 + x 5*x 13 + x 7*x 12 + x 8*x 11
def fullAdjointRoot22Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 3*y 6 + x 6*y 3) + (isotropyCross x y 1) * (x 3*y 6 + x 6*y 3 + x 19*y 21 + x 21*y 19) + (isotropyCross x y 2) * (x 15*y 21 + x 21*y 15) + (isotropyCross x y 3) * (x 0*y 6 + x 1*y 6 + x 6*y 0 + x 6*y 1 + x 13*y 21 + x 16*y 19 + x 19*y 16 + x 21*y 13) + (isotropyCross x y 4) * (x 15*y 19 + x 19*y 15) + (isotropyCross x y 6) * (x 0*y 3 + x 1*y 3 + x 3*y 0 + x 3*y 1 + x 11*y 21 + x 14*y 19 + x 19*y 14 + x 21*y 11) + (isotropyCross x y 7) * (x 10*y 21 + x 21*y 10) + (isotropyCross x y 9) * (x 10*y 19 + x 19*y 10) + (isotropyCross x y 10) * (x 1*y 15 + x 3*y 25 + x 6*y 23 + x 15*y 1 + x 23*y 6 + x 25*y 3) + (isotropyCross x y 11) * (x 6*y 21 + x 21*y 6) + (isotropyCross x y 13) * (x 3*y 21 + x 21*y 3) + (isotropyCross x y 14) * (x 6*y 19 + x 19*y 6) + (isotropyCross x y 15) * (x 1*y 10 + x 3*y 20 + x 6*y 18 + x 10*y 1 + x 18*y 6 + x 20*y 3) + (isotropyCross x y 16) * (x 3*y 19 + x 19*y 3) + (isotropyCross x y 18) * (x 6*y 15 + x 15*y 6) + (isotropyCross x y 19) * (x 0*y 21 + x 4*y 15 + x 9*y 10 + x 10*y 9 + x 15*y 4 + x 21*y 0) + (isotropyCross x y 20) * (x 3*y 15 + x 15*y 3) + (isotropyCross x y 21) * (x 0*y 19 + x 2*y 15 + x 7*y 10 + x 10*y 7 + x 15*y 2 + x 19*y 0) + (isotropyCross x y 23) * (x 6*y 10 + x 10*y 6) + (isotropyCross x y 25) * (x 3*y 10 + x 10*y 3)

theorem fullAdjointRoot22_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 4 = fullAdjointRoot22 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot22,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot22_actual (u : TraceZero F) :
    (adjoint u.val).2 2 4 = fullAdjointRoot22 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot22_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot22_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot22 (isotropyRawStar x y) = fullAdjointRoot22Certificate x y := by
  simp only [fullAdjointRoot22, isotropyRawStar, fullAdjointRoot22Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root22_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 4 = 0 := by
  rw [fullAdjointRoot22_actual,isotropyRawStar_actual,fullAdjointRoot22_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot22Certificate,hc,hp]
end Atlas.ReeF4
