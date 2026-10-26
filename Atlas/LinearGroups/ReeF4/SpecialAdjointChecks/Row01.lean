import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row00

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointDiag1 (x : Fin 26 → F) : F := x 1^2 + x 0*x 1 + x 10*x 17 + x 11*x 16 + x 12*x 15 + x 13*x 14
def fullAdjointDiag1Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 1*y 0 + x 2*y 9 + x 3*y 8 + x 4*y 7 + x 7*y 4 + x 8*y 3 + x 9*y 2 + x 14*y 13 + x 15*y 12 + x 16*y 11 + x 17*y 10 + x 18*y 25 + x 19*y 24 + x 20*y 23 + x 22*y 21) + (isotropyCross x y 1) * (x 0*y 1 + x 5*y 6 + x 7*y 4 + x 8*y 3 + x 9*y 2 + x 13*y 14 + x 14*y 13 + x 18*y 25 + x 19*y 24 + x 20*y 23 + x 21*y 22) + (isotropyCross x y 2) * (x 1*y 9 + x 9*y 0 + x 9*y 1 + x 14*y 25 + x 17*y 21 + x 23*y 16 + x 24*y 15) + (isotropyCross x y 3) * (x 0*y 8 + x 1*y 8 + x 8*y 1 + x 13*y 24 + x 17*y 20 + x 22*y 16 + x 25*y 12) + (isotropyCross x y 4) * (x 0*y 7 + x 1*y 7 + x 7*y 1 + x 13*y 23 + x 17*y 19 + x 22*y 15 + x 25*y 11) + (isotropyCross x y 5) * (x 6*y 0 + x 15*y 20 + x 16*y 19 + x 21*y 13 + x 25*y 10) + (isotropyCross x y 6) * (x 5*y 0 + x 11*y 24 + x 12*y 23 + x 18*y 17 + x 22*y 14) + (isotropyCross x y 7) * (x 0*y 4 + x 1*y 4 + x 4*y 1 + x 10*y 24 + x 14*y 20 + x 18*y 16 + x 21*y 12) + (isotropyCross x y 8) * (x 0*y 3 + x 1*y 3 + x 3*y 1 + x 10*y 23 + x 14*y 19 + x 18*y 15 + x 21*y 11) + (isotropyCross x y 9) * (x 1*y 2 + x 2*y 0 + x 2*y 1 + x 10*y 22 + x 13*y 18 + x 19*y 12 + x 20*y 11) + (isotropyCross x y 10) * (x 1*y 17 + x 5*y 25 + x 9*y 22 + x 23*y 8 + x 24*y 7) + (isotropyCross x y 11) * (x 6*y 24 + x 9*y 20 + x 16*y 1 + x 21*y 8 + x 25*y 4) + (isotropyCross x y 12) * (x 6*y 23 + x 9*y 19 + x 15*y 1 + x 21*y 7 + x 25*y 3) + (isotropyCross x y 13) * (x 1*y 14 + x 5*y 21 + x 9*y 18 + x 23*y 4 + x 24*y 3) + (isotropyCross x y 14) * (x 1*y 13 + x 2*y 25 + x 6*y 22 + x 19*y 8 + x 20*y 7) + (isotropyCross x y 15) * (x 2*y 24 + x 5*y 20 + x 12*y 1 + x 18*y 8 + x 22*y 4) + (isotropyCross x y 16) * (x 2*y 23 + x 5*y 19 + x 11*y 1 + x 18*y 7 + x 22*y 3) + (isotropyCross x y 17) * (x 1*y 10 + x 2*y 21 + x 6*y 18 + x 19*y 4 + x 20*y 3) + (isotropyCross x y 18) * (x 6*y 17 + x 9*y 13 + x 15*y 8 + x 16*y 7) + (isotropyCross x y 19) * (x 0*y 24 + x 4*y 17 + x 8*y 14 + x 12*y 9 + x 16*y 5 + x 24*y 0) + (isotropyCross x y 20) * (x 0*y 23 + x 3*y 17 + x 7*y 14 + x 11*y 9 + x 15*y 5 + x 23*y 0) + (isotropyCross x y 21) * (x 2*y 17 + x 5*y 13 + x 11*y 8 + x 12*y 7) + (isotropyCross x y 22) * (x 6*y 14 + x 9*y 10 + x 15*y 4 + x 16*y 3) + (isotropyCross x y 23) * (x 0*y 20 + x 4*y 13 + x 8*y 10 + x 12*y 6 + x 16*y 2 + x 20*y 0) + (isotropyCross x y 24) * (x 0*y 19 + x 3*y 13 + x 7*y 10 + x 11*y 6 + x 15*y 2 + x 19*y 0) + (isotropyCross x y 25) * (x 2*y 14 + x 5*y 10 + x 11*y 4 + x 12*y 3) + (isotropyPolar x y) * (x 0*y 1 + x 1*y 0 + x 2*y 9 + x 3*y 8 + x 4*y 7 + x 5*y 6 + x 6*y 5 + x 7*y 4 + x 8*y 3 + x 9*y 2)

theorem fullAdjointDiag1_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).1 1 = fullAdjointDiag1 x := by
  simp [adjoint,isotropyPoint,fullAdjointDiag1,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointDiag1_actual (u : TraceZero F) :
    (adjoint u.val).1 1 = fullAdjointDiag1 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointDiag1_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointDiag1_quartic_identity (x y : Fin 26 → F) :
    fullAdjointDiag1 (isotropyRawStar x y) = fullAdjointDiag1Certificate x y := by
  simp only [fullAdjointDiag1, isotropyRawStar, fullAdjointDiag1Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_diag1_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).1 1 = 0 := by
  rw [fullAdjointDiag1_actual,isotropyRawStar_actual,fullAdjointDiag1_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointDiag1Certificate,hc,hp]
end Atlas.ReeF4
