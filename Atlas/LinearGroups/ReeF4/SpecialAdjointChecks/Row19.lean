import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row18

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot18 (x : Fin 26 → F) : F := x 0*x 18 + x 1*x 18 + x 2*x 14 + x 3*x 12 + x 4*x 11 + x 5*x 10
def fullAdjointRoot18Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 10*y 12 + x 12*y 10 + x 18*y 20 + x 20*y 18) + (isotropyCross x y 1) * (x 2*y 4 + x 4*y 2 + x 18*y 20 + x 20*y 18) + (isotropyCross x y 2) * (x 0*y 4 + x 1*y 4 + x 4*y 0 + x 4*y 1 + x 14*y 20 + x 16*y 18 + x 18*y 16 + x 20*y 14) + (isotropyCross x y 3) * (x 12*y 20 + x 20*y 12) + (isotropyCross x y 4) * (x 0*y 2 + x 1*y 2 + x 2*y 0 + x 2*y 1 + x 11*y 20 + x 13*y 18 + x 18*y 13 + x 20*y 11) + (isotropyCross x y 5) * (x 10*y 20 + x 20*y 10) + (isotropyCross x y 6) * (x 12*y 18 + x 18*y 12) + (isotropyCross x y 8) * (x 10*y 18 + x 18*y 10) + (isotropyCross x y 10) * (x 0*y 12 + x 1*y 12 + x 5*y 20 + x 8*y 18 + x 12*y 0 + x 12*y 1 + x 18*y 8 + x 20*y 5) + (isotropyCross x y 11) * (x 4*y 20 + x 20*y 4) + (isotropyCross x y 12) * (x 0*y 10 + x 1*y 10 + x 3*y 20 + x 6*y 18 + x 10*y 0 + x 10*y 1 + x 18*y 6 + x 20*y 3) + (isotropyCross x y 13) * (x 4*y 18 + x 18*y 4) + (isotropyCross x y 14) * (x 2*y 20 + x 20*y 2) + (isotropyCross x y 16) * (x 2*y 18 + x 18*y 2) + (isotropyCross x y 18) * (x 0*y 20 + x 6*y 12 + x 8*y 10 + x 10*y 8 + x 12*y 6 + x 20*y 0) + (isotropyCross x y 19) * (x 4*y 12 + x 12*y 4) + (isotropyCross x y 20) * (x 0*y 18 + x 3*y 12 + x 5*y 10 + x 10*y 5 + x 12*y 3 + x 18*y 0) + (isotropyCross x y 21) * (x 2*y 12 + x 12*y 2) + (isotropyCross x y 22) * (x 4*y 10 + x 10*y 4) + (isotropyCross x y 24) * (x 2*y 10 + x 10*y 2)

theorem fullAdjointRoot18_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 0 = fullAdjointRoot18 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot18,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot18_actual (u : TraceZero F) :
    (adjoint u.val).2 2 0 = fullAdjointRoot18 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot18_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot18_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot18 (isotropyRawStar x y) = fullAdjointRoot18Certificate x y := by
  simp only [fullAdjointRoot18, isotropyRawStar, fullAdjointRoot18Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root18_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 0 = 0 := by
  rw [fullAdjointRoot18_actual,isotropyRawStar_actual,fullAdjointRoot18_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot18Certificate,hc,hp]
end Atlas.ReeF4
