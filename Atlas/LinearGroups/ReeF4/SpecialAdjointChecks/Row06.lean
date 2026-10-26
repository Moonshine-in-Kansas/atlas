import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row05

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot5 (x : Fin 26 → F) : F := x 1*x 5 + x 11*x 24 + x 12*x 23 + x 14*x 22 + x 17*x 18
def fullAdjointRoot5Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 4*y 6 + x 6*y 4) + (isotropyCross x y 1) * (x 4*y 6 + x 6*y 4 + x 20*y 21 + x 21*y 20) + (isotropyCross x y 2) * (x 16*y 21 + x 21*y 16) + (isotropyCross x y 3) * (x 16*y 20 + x 20*y 16) + (isotropyCross x y 4) * (x 0*y 6 + x 1*y 6 + x 6*y 0 + x 6*y 1 + x 13*y 21 + x 15*y 20 + x 20*y 15 + x 21*y 13) + (isotropyCross x y 6) * (x 0*y 4 + x 1*y 4 + x 4*y 0 + x 4*y 1 + x 12*y 21 + x 14*y 20 + x 20*y 14 + x 21*y 12) + (isotropyCross x y 8) * (x 10*y 21 + x 21*y 10) + (isotropyCross x y 9) * (x 10*y 20 + x 20*y 10) + (isotropyCross x y 10) * (x 1*y 16 + x 4*y 25 + x 6*y 24 + x 16*y 1 + x 24*y 6 + x 25*y 4) + (isotropyCross x y 12) * (x 6*y 21 + x 21*y 6) + (isotropyCross x y 13) * (x 4*y 21 + x 21*y 4) + (isotropyCross x y 14) * (x 6*y 20 + x 20*y 6) + (isotropyCross x y 15) * (x 4*y 20 + x 20*y 4) + (isotropyCross x y 16) * (x 1*y 10 + x 4*y 19 + x 6*y 18 + x 10*y 1 + x 18*y 6 + x 19*y 4) + (isotropyCross x y 18) * (x 6*y 16 + x 16*y 6) + (isotropyCross x y 19) * (x 4*y 16 + x 16*y 4) + (isotropyCross x y 20) * (x 0*y 21 + x 3*y 16 + x 9*y 10 + x 10*y 9 + x 16*y 3 + x 21*y 0) + (isotropyCross x y 21) * (x 0*y 20 + x 2*y 16 + x 8*y 10 + x 10*y 8 + x 16*y 2 + x 20*y 0) + (isotropyCross x y 24) * (x 6*y 10 + x 10*y 6) + (isotropyCross x y 25) * (x 4*y 10 + x 10*y 4)

theorem fullAdjointRoot5_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 3 = fullAdjointRoot5 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot5,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot5_actual (u : TraceZero F) :
    (adjoint u.val).2 0 3 = fullAdjointRoot5 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot5_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot5_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot5 (isotropyRawStar x y) = fullAdjointRoot5Certificate x y := by
  simp only [fullAdjointRoot5, isotropyRawStar, fullAdjointRoot5Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root5_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 3 = 0 := by
  rw [fullAdjointRoot5_actual,isotropyRawStar_actual,fullAdjointRoot5_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot5Certificate,hc,hp]
end Atlas.ReeF4
