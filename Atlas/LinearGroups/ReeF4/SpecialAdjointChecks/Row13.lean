import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row12

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot12 (x : Fin 26 → F) : F := x 0*x 12 + x 2*x 24 + x 4*x 22 + x 5*x 20 + x 8*x 18
def fullAdjointRoot12Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 10*y 14 + x 14*y 10 + x 18*y 21 + x 21*y 18) + (isotropyCross x y 1) * (x 10*y 14 + x 14*y 10) + (isotropyCross x y 2) * (x 14*y 21 + x 21*y 14) + (isotropyCross x y 3) * (x 0*y 4 + x 1*y 4 + x 4*y 0 + x 4*y 1 + x 12*y 21 + x 16*y 18 + x 18*y 16 + x 21*y 12) + (isotropyCross x y 4) * (x 0*y 3 + x 1*y 3 + x 3*y 0 + x 3*y 1 + x 11*y 21 + x 15*y 18 + x 18*y 15 + x 21*y 11) + (isotropyCross x y 5) * (x 10*y 21 + x 21*y 10) + (isotropyCross x y 6) * (x 14*y 18 + x 18*y 14) + (isotropyCross x y 9) * (x 10*y 18 + x 18*y 10) + (isotropyCross x y 10) * (x 1*y 14 + x 3*y 24 + x 4*y 23 + x 14*y 1 + x 23*y 4 + x 24*y 3) + (isotropyCross x y 11) * (x 4*y 21 + x 21*y 4) + (isotropyCross x y 12) * (x 3*y 21 + x 21*y 3) + (isotropyCross x y 14) * (x 1*y 10 + x 3*y 20 + x 4*y 19 + x 10*y 1 + x 19*y 4 + x 20*y 3) + (isotropyCross x y 15) * (x 4*y 18 + x 18*y 4) + (isotropyCross x y 16) * (x 3*y 18 + x 18*y 3) + (isotropyCross x y 18) * (x 0*y 21 + x 6*y 14 + x 9*y 10 + x 10*y 9 + x 14*y 6 + x 21*y 0) + (isotropyCross x y 19) * (x 4*y 14 + x 14*y 4) + (isotropyCross x y 20) * (x 3*y 14 + x 14*y 3) + (isotropyCross x y 21) * (x 0*y 18 + x 2*y 14 + x 5*y 10 + x 10*y 5 + x 14*y 2 + x 18*y 0) + (isotropyCross x y 23) * (x 4*y 10 + x 10*y 4) + (isotropyCross x y 24) * (x 3*y 10 + x 10*y 3) + (isotropyPolar x y) * (x 3*y 4 + x 4*y 3 + x 10*y 14 + x 14*y 10 + x 18*y 21 + x 21*y 18)

theorem fullAdjointRoot12_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 2 = fullAdjointRoot12 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot12,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot12_actual (u : TraceZero F) :
    (adjoint u.val).2 1 2 = fullAdjointRoot12 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot12_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot12_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot12 (isotropyRawStar x y) = fullAdjointRoot12Certificate x y := by
  simp only [fullAdjointRoot12, isotropyRawStar, fullAdjointRoot12Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root12_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 2 = 0 := by
  rw [fullAdjointRoot12_actual,isotropyRawStar_actual,fullAdjointRoot12_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot12Certificate,hc,hp]
end Atlas.ReeF4
