import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row08

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot8 (x : Fin 26 → F) : F := x 1*x 8 + x 12*x 25 + x 13*x 24 + x 16*x 22 + x 17*x 20
def fullAdjointRoot8Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 14*y 15 + x 15*y 14 + x 21*y 23 + x 23*y 21) + (isotropyCross x y 1) * (x 14*y 15 + x 15*y 14) + (isotropyCross x y 3) * (x 0*y 9 + x 9*y 0 + x 14*y 25 + x 15*y 24 + x 24*y 15 + x 25*y 14) + (isotropyCross x y 4) * (x 15*y 23 + x 23*y 15) + (isotropyCross x y 5) * (x 15*y 21 + x 21*y 15) + (isotropyCross x y 6) * (x 14*y 23 + x 23*y 14) + (isotropyCross x y 7) * (x 14*y 21 + x 21*y 14) + (isotropyCross x y 9) * (x 0*y 3 + x 3*y 0 + x 14*y 19 + x 15*y 18 + x 18*y 15 + x 19*y 14) + (isotropyCross x y 10) * (x 9*y 23 + x 23*y 9) + (isotropyCross x y 11) * (x 9*y 21 + x 21*y 9) + (isotropyCross x y 14) * (x 0*y 15 + x 1*y 15 + x 6*y 23 + x 7*y 21 + x 15*y 0 + x 15*y 1 + x 21*y 7 + x 23*y 6) + (isotropyCross x y 15) * (x 0*y 14 + x 1*y 14 + x 4*y 23 + x 5*y 21 + x 14*y 0 + x 14*y 1 + x 21*y 5 + x 23*y 4) + (isotropyCross x y 16) * (x 3*y 23 + x 23*y 3) + (isotropyCross x y 17) * (x 3*y 21 + x 21*y 3) + (isotropyCross x y 18) * (x 9*y 15 + x 15*y 9) + (isotropyCross x y 19) * (x 9*y 14 + x 14*y 9) + (isotropyCross x y 21) * (x 0*y 23 + x 5*y 15 + x 7*y 14 + x 14*y 7 + x 15*y 5 + x 23*y 0) + (isotropyCross x y 23) * (x 0*y 21 + x 4*y 15 + x 6*y 14 + x 14*y 6 + x 15*y 4 + x 21*y 0) + (isotropyCross x y 24) * (x 3*y 15 + x 15*y 3) + (isotropyCross x y 25) * (x 3*y 14 + x 14*y 3)

theorem fullAdjointRoot8_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 6 = fullAdjointRoot8 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot8,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot8_actual (u : TraceZero F) :
    (adjoint u.val).2 0 6 = fullAdjointRoot8 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot8_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot8_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot8 (isotropyRawStar x y) = fullAdjointRoot8Certificate x y := by
  simp only [fullAdjointRoot8, isotropyRawStar, fullAdjointRoot8Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root8_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 6 = 0 := by
  rw [fullAdjointRoot8_actual,isotropyRawStar_actual,fullAdjointRoot8_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot8Certificate,hc,hp]
end Atlas.ReeF4
