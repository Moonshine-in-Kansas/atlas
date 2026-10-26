import Atlas.LinearGroups.ReeF4.SpecialAdjointTop

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointDiag0 (x : Fin 26 → F) : F := x 0^2 + x 0*x 1 + x 2*x 9 + x 3*x 8 + x 4*x 7 + x 5*x 6
def fullAdjointDiag0Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 0*y 1 + x 2*y 9 + x 3*y 8 + x 4*y 7 + x 7*y 4 + x 8*y 3 + x 9*y 2 + x 11*y 16 + x 13*y 14 + x 15*y 12 + x 17*y 10 + x 18*y 25 + x 20*y 23 + x 21*y 22 + x 24*y 19) + (isotropyCross x y 1) * (x 0*y 1 + x 3*y 8 + x 6*y 5 + x 7*y 4 + x 9*y 2 + x 13*y 14 + x 14*y 13 + x 18*y 25 + x 20*y 23 + x 22*y 21 + x 24*y 19) + (isotropyCross x y 2) * (x 9*y 0 + x 16*y 23 + x 17*y 21 + x 24*y 15 + x 25*y 14) + (isotropyCross x y 3) * (x 8*y 0 + x 16*y 22 + x 17*y 20 + x 24*y 13 + x 25*y 12) + (isotropyCross x y 4) * (x 0*y 7 + x 11*y 25 + x 17*y 19 + x 22*y 15 + x 23*y 13) + (isotropyCross x y 5) * (x 0*y 6 + x 10*y 25 + x 16*y 19 + x 20*y 15 + x 21*y 13) + (isotropyCross x y 6) * (x 0*y 5 + x 11*y 24 + x 17*y 18 + x 22*y 14 + x 23*y 12) + (isotropyCross x y 7) * (x 0*y 4 + x 10*y 24 + x 16*y 18 + x 20*y 14 + x 21*y 12) + (isotropyCross x y 8) * (x 3*y 0 + x 10*y 23 + x 11*y 21 + x 18*y 15 + x 19*y 14) + (isotropyCross x y 9) * (x 2*y 0 + x 10*y 22 + x 11*y 20 + x 18*y 13 + x 19*y 12) + (isotropyCross x y 10) * (x 8*y 23 + x 9*y 22 + x 17*y 1 + x 24*y 7 + x 25*y 5) + (isotropyCross x y 11) * (x 8*y 21 + x 9*y 20 + x 16*y 1 + x 24*y 6 + x 25*y 4) + (isotropyCross x y 12) * (x 1*y 15 + x 3*y 25 + x 9*y 19 + x 21*y 7 + x 23*y 6) + (isotropyCross x y 13) * (x 1*y 14 + x 3*y 24 + x 9*y 18 + x 21*y 5 + x 23*y 4) + (isotropyCross x y 14) * (x 1*y 13 + x 2*y 25 + x 8*y 19 + x 20*y 7 + x 22*y 6) + (isotropyCross x y 15) * (x 1*y 12 + x 2*y 24 + x 8*y 18 + x 20*y 5 + x 22*y 4) + (isotropyCross x y 16) * (x 2*y 23 + x 3*y 22 + x 11*y 1 + x 18*y 7 + x 19*y 5) + (isotropyCross x y 17) * (x 2*y 21 + x 3*y 20 + x 10*y 1 + x 18*y 6 + x 19*y 4) + (isotropyCross x y 18) * (x 8*y 15 + x 9*y 13 + x 16*y 7 + x 17*y 6) + (isotropyCross x y 19) * (x 8*y 14 + x 9*y 12 + x 16*y 5 + x 17*y 4) + (isotropyCross x y 20) * (x 0*y 23 + x 5*y 15 + x 7*y 14 + x 11*y 9 + x 17*y 3 + x 23*y 0) + (isotropyCross x y 21) * (x 0*y 22 + x 5*y 13 + x 7*y 12 + x 11*y 8 + x 17*y 2 + x 22*y 0) + (isotropyCross x y 22) * (x 0*y 21 + x 4*y 15 + x 6*y 14 + x 10*y 9 + x 16*y 3 + x 21*y 0) + (isotropyCross x y 23) * (x 0*y 20 + x 4*y 13 + x 6*y 12 + x 10*y 8 + x 16*y 2 + x 20*y 0) + (isotropyCross x y 24) * (x 2*y 15 + x 3*y 13 + x 10*y 7 + x 11*y 6) + (isotropyCross x y 25) * (x 2*y 14 + x 3*y 12 + x 10*y 5 + x 11*y 4) + (isotropyPolar x y) * (x 2*y 9 + x 4*y 7 + x 7*y 4 + x 9*y 2 + x 11*y 16 + x 13*y 14 + x 14*y 13 + x 16*y 11 + x 19*y 24 + x 21*y 22 + x 22*y 21 + x 24*y 19)

theorem fullAdjointDiag0_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).1 0 = fullAdjointDiag0 x := by
  simp [adjoint,isotropyPoint,fullAdjointDiag0,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointDiag0_actual (u : TraceZero F) :
    (adjoint u.val).1 0 = fullAdjointDiag0 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointDiag0_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointDiag0_quartic_identity (x y : Fin 26 → F) :
    fullAdjointDiag0 (isotropyRawStar x y) = fullAdjointDiag0Certificate x y := by
  simp only [fullAdjointDiag0, isotropyRawStar, fullAdjointDiag0Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_diag0_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).1 0 = 0 := by
  rw [fullAdjointDiag0_actual,isotropyRawStar_actual,fullAdjointDiag0_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointDiag0Certificate,hc,hp]
end Atlas.ReeF4
