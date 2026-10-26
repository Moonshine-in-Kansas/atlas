import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row04

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot4 (x : Fin 26 → F) : F := x 1*x 4 + x 10*x 24 + x 12*x 21 + x 14*x 20 + x 16*x 18
def fullAdjointRoot4Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 4*y 5 + x 5*y 4) + (isotropyCross x y 1) * (x 12*y 14 + x 14*y 12) + (isotropyCross x y 2) * (x 14*y 24 + x 24*y 14) + (isotropyCross x y 3) * (x 12*y 24 + x 24*y 12) + (isotropyCross x y 4) * (x 0*y 5 + x 5*y 0 + x 12*y 23 + x 14*y 22 + x 22*y 14 + x 23*y 12) + (isotropyCross x y 5) * (x 0*y 4 + x 4*y 0 + x 12*y 21 + x 14*y 20 + x 20*y 14 + x 21*y 12) + (isotropyCross x y 8) * (x 14*y 18 + x 18*y 14) + (isotropyCross x y 9) * (x 12*y 18 + x 18*y 12) + (isotropyCross x y 10) * (x 5*y 24 + x 24*y 5) + (isotropyCross x y 11) * (x 4*y 24 + x 24*y 4) + (isotropyCross x y 12) * (x 1*y 14 + x 4*y 23 + x 5*y 21 + x 14*y 1 + x 21*y 5 + x 23*y 4) + (isotropyCross x y 14) * (x 1*y 12 + x 4*y 22 + x 5*y 20 + x 12*y 1 + x 20*y 5 + x 22*y 4) + (isotropyCross x y 16) * (x 5*y 18 + x 18*y 5) + (isotropyCross x y 17) * (x 4*y 18 + x 18*y 4) + (isotropyCross x y 18) * (x 0*y 24 + x 8*y 14 + x 9*y 12 + x 12*y 9 + x 14*y 8 + x 24*y 0) + (isotropyCross x y 20) * (x 5*y 14 + x 14*y 5) + (isotropyCross x y 21) * (x 5*y 12 + x 12*y 5) + (isotropyCross x y 22) * (x 4*y 14 + x 14*y 4) + (isotropyCross x y 23) * (x 4*y 12 + x 12*y 4) + (isotropyCross x y 24) * (x 0*y 18 + x 2*y 14 + x 3*y 12 + x 12*y 3 + x 14*y 2 + x 18*y 0)

theorem fullAdjointRoot4_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 2 = fullAdjointRoot4 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot4,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot4_actual (u : TraceZero F) :
    (adjoint u.val).2 0 2 = fullAdjointRoot4 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot4_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot4_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot4 (isotropyRawStar x y) = fullAdjointRoot4Certificate x y := by
  simp only [fullAdjointRoot4, isotropyRawStar, fullAdjointRoot4Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root4_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 2 = 0 := by
  rw [fullAdjointRoot4_actual,isotropyRawStar_actual,fullAdjointRoot4_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot4Certificate,hc,hp]
end Atlas.ReeF4
