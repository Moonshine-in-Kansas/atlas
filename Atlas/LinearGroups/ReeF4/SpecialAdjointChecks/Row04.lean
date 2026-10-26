import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row03

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot3 (x : Fin 26 → F) : F := x 1*x 3 + x 10*x 23 + x 11*x 21 + x 14*x 19 + x 15*x 18
def fullAdjointRoot3Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 12*y 13 + x 13*y 12 + x 20*y 22 + x 22*y 20) + (isotropyCross x y 1) * (x 12*y 13 + x 13*y 12) + (isotropyCross x y 2) * (x 0*y 8 + x 8*y 0 + x 12*y 25 + x 13*y 24 + x 24*y 13 + x 25*y 12) + (isotropyCross x y 4) * (x 13*y 22 + x 22*y 13) + (isotropyCross x y 5) * (x 13*y 20 + x 20*y 13) + (isotropyCross x y 6) * (x 12*y 22 + x 22*y 12) + (isotropyCross x y 7) * (x 12*y 20 + x 20*y 12) + (isotropyCross x y 8) * (x 0*y 2 + x 2*y 0 + x 12*y 19 + x 13*y 18 + x 18*y 13 + x 19*y 12) + (isotropyCross x y 10) * (x 8*y 22 + x 22*y 8) + (isotropyCross x y 11) * (x 8*y 20 + x 20*y 8) + (isotropyCross x y 12) * (x 0*y 13 + x 1*y 13 + x 6*y 22 + x 7*y 20 + x 13*y 0 + x 13*y 1 + x 20*y 7 + x 22*y 6) + (isotropyCross x y 13) * (x 0*y 12 + x 1*y 12 + x 4*y 22 + x 5*y 20 + x 12*y 0 + x 12*y 1 + x 20*y 5 + x 22*y 4) + (isotropyCross x y 16) * (x 2*y 22 + x 22*y 2) + (isotropyCross x y 17) * (x 2*y 20 + x 20*y 2) + (isotropyCross x y 18) * (x 8*y 13 + x 13*y 8) + (isotropyCross x y 19) * (x 8*y 12 + x 12*y 8) + (isotropyCross x y 20) * (x 0*y 22 + x 5*y 13 + x 7*y 12 + x 12*y 7 + x 13*y 5 + x 22*y 0) + (isotropyCross x y 22) * (x 0*y 20 + x 4*y 13 + x 6*y 12 + x 12*y 6 + x 13*y 4 + x 20*y 0) + (isotropyCross x y 24) * (x 2*y 13 + x 13*y 2) + (isotropyCross x y 25) * (x 2*y 12 + x 12*y 2)

theorem fullAdjointRoot3_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 1 = fullAdjointRoot3 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot3,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot3_actual (u : TraceZero F) :
    (adjoint u.val).2 0 1 = fullAdjointRoot3 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot3_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot3_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot3 (isotropyRawStar x y) = fullAdjointRoot3Certificate x y := by
  simp only [fullAdjointRoot3, isotropyRawStar, fullAdjointRoot3Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root3_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 1 = 0 := by
  rw [fullAdjointRoot3_actual,isotropyRawStar_actual,fullAdjointRoot3_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot3Certificate,hc,hp]
end Atlas.ReeF4
