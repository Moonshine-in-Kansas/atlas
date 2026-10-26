import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row02

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot2 (x : Fin 26 → F) : F := x 1*x 2 + x 10*x 22 + x 11*x 20 + x 12*x 19 + x 13*x 18
def fullAdjointRoot2Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 10*y 11 + x 11*y 10 + x 18*y 19 + x 19*y 18) + (isotropyCross x y 1) * (x 2*y 3 + x 3*y 2 + x 18*y 19 + x 19*y 18) + (isotropyCross x y 2) * (x 0*y 3 + x 1*y 3 + x 3*y 0 + x 3*y 1 + x 14*y 19 + x 15*y 18 + x 18*y 15 + x 19*y 14) + (isotropyCross x y 3) * (x 0*y 2 + x 1*y 2 + x 2*y 0 + x 2*y 1 + x 12*y 19 + x 13*y 18 + x 18*y 13 + x 19*y 12) + (isotropyCross x y 4) * (x 11*y 19 + x 19*y 11) + (isotropyCross x y 5) * (x 10*y 19 + x 19*y 10) + (isotropyCross x y 6) * (x 11*y 18 + x 18*y 11) + (isotropyCross x y 7) * (x 10*y 18 + x 18*y 10) + (isotropyCross x y 10) * (x 0*y 11 + x 1*y 11 + x 5*y 19 + x 7*y 18 + x 11*y 0 + x 11*y 1 + x 18*y 7 + x 19*y 5) + (isotropyCross x y 11) * (x 0*y 10 + x 1*y 10 + x 4*y 19 + x 6*y 18 + x 10*y 0 + x 10*y 1 + x 18*y 6 + x 19*y 4) + (isotropyCross x y 12) * (x 3*y 19 + x 19*y 3) + (isotropyCross x y 13) * (x 3*y 18 + x 18*y 3) + (isotropyCross x y 14) * (x 2*y 19 + x 19*y 2) + (isotropyCross x y 15) * (x 2*y 18 + x 18*y 2) + (isotropyCross x y 18) * (x 0*y 19 + x 6*y 11 + x 7*y 10 + x 10*y 7 + x 11*y 6 + x 19*y 0) + (isotropyCross x y 19) * (x 0*y 18 + x 4*y 11 + x 5*y 10 + x 10*y 5 + x 11*y 4 + x 18*y 0) + (isotropyCross x y 20) * (x 3*y 11 + x 11*y 3) + (isotropyCross x y 21) * (x 2*y 11 + x 11*y 2) + (isotropyCross x y 22) * (x 3*y 10 + x 10*y 3) + (isotropyCross x y 23) * (x 2*y 10 + x 10*y 2)

theorem fullAdjointRoot2_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 0 = fullAdjointRoot2 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot2,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot2_actual (u : TraceZero F) :
    (adjoint u.val).2 0 0 = fullAdjointRoot2 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot2_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot2_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot2 (isotropyRawStar x y) = fullAdjointRoot2Certificate x y := by
  simp only [fullAdjointRoot2, isotropyRawStar, fullAdjointRoot2Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root2_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 0 = 0 := by
  rw [fullAdjointRoot2_actual,isotropyRawStar_actual,fullAdjointRoot2_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot2Certificate,hc,hp]
end Atlas.ReeF4
