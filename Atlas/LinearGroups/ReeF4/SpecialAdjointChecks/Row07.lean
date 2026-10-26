import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row06

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot6 (x : Fin 26 → F) : F := x 1*x 6 + x 10*x 25 + x 13*x 21 + x 15*x 20 + x 16*x 19
def fullAdjointRoot6Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 5*y 7 + x 7*y 5) + (isotropyCross x y 1) * (x 5*y 7 + x 7*y 5 + x 22*y 23 + x 23*y 22) + (isotropyCross x y 2) * (x 17*y 23 + x 23*y 17) + (isotropyCross x y 3) * (x 17*y 22 + x 22*y 17) + (isotropyCross x y 5) * (x 0*y 7 + x 1*y 7 + x 7*y 0 + x 7*y 1 + x 13*y 23 + x 15*y 22 + x 22*y 15 + x 23*y 13) + (isotropyCross x y 7) * (x 0*y 5 + x 1*y 5 + x 5*y 0 + x 5*y 1 + x 12*y 23 + x 14*y 22 + x 22*y 14 + x 23*y 12) + (isotropyCross x y 8) * (x 11*y 23 + x 23*y 11) + (isotropyCross x y 9) * (x 11*y 22 + x 22*y 11) + (isotropyCross x y 11) * (x 1*y 17 + x 5*y 25 + x 7*y 24 + x 17*y 1 + x 24*y 7 + x 25*y 5) + (isotropyCross x y 12) * (x 7*y 23 + x 23*y 7) + (isotropyCross x y 13) * (x 5*y 23 + x 23*y 5) + (isotropyCross x y 14) * (x 7*y 22 + x 22*y 7) + (isotropyCross x y 15) * (x 5*y 22 + x 22*y 5) + (isotropyCross x y 17) * (x 1*y 11 + x 5*y 19 + x 7*y 18 + x 11*y 1 + x 18*y 7 + x 19*y 5) + (isotropyCross x y 18) * (x 7*y 17 + x 17*y 7) + (isotropyCross x y 19) * (x 5*y 17 + x 17*y 5) + (isotropyCross x y 22) * (x 0*y 23 + x 3*y 17 + x 9*y 11 + x 11*y 9 + x 17*y 3 + x 23*y 0) + (isotropyCross x y 23) * (x 0*y 22 + x 2*y 17 + x 8*y 11 + x 11*y 8 + x 17*y 2 + x 22*y 0) + (isotropyCross x y 24) * (x 7*y 11 + x 11*y 7) + (isotropyCross x y 25) * (x 5*y 11 + x 11*y 5)

theorem fullAdjointRoot6_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 4 = fullAdjointRoot6 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot6,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot6_actual (u : TraceZero F) :
    (adjoint u.val).2 0 4 = fullAdjointRoot6 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot6_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot6_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot6 (isotropyRawStar x y) = fullAdjointRoot6Certificate x y := by
  simp only [fullAdjointRoot6, isotropyRawStar, fullAdjointRoot6Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root6_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 4 = 0 := by
  rw [fullAdjointRoot6_actual,isotropyRawStar_actual,fullAdjointRoot6_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot6Certificate,hc,hp]
end Atlas.ReeF4
