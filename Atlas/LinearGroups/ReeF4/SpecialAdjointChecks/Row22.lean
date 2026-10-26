import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row21

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot21 (x : Fin 26 → F) : F := x 0*x 21 + x 1*x 21 + x 3*x 16 + x 4*x 15 + x 6*x 14 + x 9*x 10
def fullAdjointRoot21Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 5*y 8 + x 8*y 5) + (isotropyCross x y 1) * (x 5*y 8 + x 8*y 5 + x 22*y 24 + x 24*y 22) + (isotropyCross x y 2) * (x 17*y 24 + x 24*y 17) + (isotropyCross x y 4) * (x 17*y 22 + x 22*y 17) + (isotropyCross x y 5) * (x 0*y 8 + x 8*y 0 + x 12*y 25 + x 17*y 20 + x 20*y 17 + x 25*y 12) + (isotropyCross x y 7) * (x 12*y 24 + x 24*y 12) + (isotropyCross x y 8) * (x 0*y 5 + x 5*y 0 + x 12*y 23 + x 17*y 18 + x 18*y 17 + x 23*y 12) + (isotropyCross x y 9) * (x 12*y 22 + x 22*y 12) + (isotropyCross x y 11) * (x 8*y 24 + x 24*y 8) + (isotropyCross x y 12) * (x 1*y 17 + x 5*y 25 + x 8*y 23 + x 17*y 1 + x 23*y 8 + x 25*y 5) + (isotropyCross x y 13) * (x 5*y 24 + x 24*y 5) + (isotropyCross x y 14) * (x 8*y 22 + x 22*y 8) + (isotropyCross x y 16) * (x 5*y 22 + x 22*y 5) + (isotropyCross x y 17) * (x 1*y 12 + x 5*y 20 + x 8*y 18 + x 12*y 1 + x 18*y 8 + x 20*y 5) + (isotropyCross x y 18) * (x 8*y 17 + x 17*y 8) + (isotropyCross x y 20) * (x 5*y 17 + x 17*y 5) + (isotropyCross x y 22) * (x 0*y 24 + x 4*y 17 + x 9*y 12 + x 12*y 9 + x 17*y 4 + x 24*y 0) + (isotropyCross x y 23) * (x 8*y 12 + x 12*y 8) + (isotropyCross x y 24) * (x 0*y 22 + x 2*y 17 + x 7*y 12 + x 12*y 7 + x 17*y 2 + x 22*y 0) + (isotropyCross x y 25) * (x 5*y 12 + x 12*y 5)

theorem fullAdjointRoot21_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 3 = fullAdjointRoot21 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot21,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot21_actual (u : TraceZero F) :
    (adjoint u.val).2 2 3 = fullAdjointRoot21 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot21_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot21_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot21 (isotropyRawStar x y) = fullAdjointRoot21Certificate x y := by
  simp only [fullAdjointRoot21, isotropyRawStar, fullAdjointRoot21Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root21_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 3 = 0 := by
  rw [fullAdjointRoot21_actual,isotropyRawStar_actual,fullAdjointRoot21_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot21Certificate,hc,hp]
end Atlas.ReeF4
