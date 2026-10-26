import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row14

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot14 (x : Fin 26 → F) : F := x 0*x 14 + x 3*x 24 + x 4*x 23 + x 5*x 21 + x 9*x 18
def fullAdjointRoot14Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 12*y 16 + x 16*y 12 + x 20*y 24 + x 24*y 20) + (isotropyCross x y 1) * (x 4*y 8 + x 8*y 4 + x 20*y 24 + x 24*y 20) + (isotropyCross x y 2) * (x 16*y 24 + x 24*y 16) + (isotropyCross x y 4) * (x 0*y 8 + x 8*y 0 + x 12*y 25 + x 16*y 22 + x 22*y 16 + x 25*y 12) + (isotropyCross x y 5) * (x 16*y 20 + x 20*y 16) + (isotropyCross x y 6) * (x 12*y 24 + x 24*y 12) + (isotropyCross x y 8) * (x 0*y 4 + x 4*y 0 + x 12*y 21 + x 16*y 18 + x 18*y 16 + x 21*y 12) + (isotropyCross x y 9) * (x 12*y 20 + x 20*y 12) + (isotropyCross x y 10) * (x 8*y 24 + x 24*y 8) + (isotropyCross x y 12) * (x 1*y 16 + x 4*y 25 + x 8*y 21 + x 16*y 1 + x 21*y 8 + x 25*y 4) + (isotropyCross x y 13) * (x 4*y 24 + x 24*y 4) + (isotropyCross x y 14) * (x 8*y 20 + x 20*y 8) + (isotropyCross x y 16) * (x 1*y 12 + x 4*y 22 + x 8*y 18 + x 12*y 1 + x 18*y 8 + x 22*y 4) + (isotropyCross x y 17) * (x 4*y 20 + x 20*y 4) + (isotropyCross x y 18) * (x 8*y 16 + x 16*y 8) + (isotropyCross x y 20) * (x 0*y 24 + x 5*y 16 + x 9*y 12 + x 12*y 9 + x 16*y 5 + x 24*y 0) + (isotropyCross x y 21) * (x 8*y 12 + x 12*y 8) + (isotropyCross x y 22) * (x 4*y 16 + x 16*y 4) + (isotropyCross x y 24) * (x 0*y 20 + x 2*y 16 + x 6*y 12 + x 12*y 6 + x 16*y 2 + x 20*y 0) + (isotropyCross x y 25) * (x 4*y 12 + x 12*y 4) + (isotropyPolar x y) * (x 4*y 8 + x 8*y 4 + x 12*y 16 + x 16*y 12 + x 20*y 24 + x 24*y 20)

theorem fullAdjointRoot14_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 4 = fullAdjointRoot14 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot14,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot14_actual (u : TraceZero F) :
    (adjoint u.val).2 1 4 = fullAdjointRoot14 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot14_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot14_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot14 (isotropyRawStar x y) = fullAdjointRoot14Certificate x y := by
  simp only [fullAdjointRoot14, isotropyRawStar, fullAdjointRoot14Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root14_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 4 = 0 := by
  rw [fullAdjointRoot14_actual,isotropyRawStar_actual,fullAdjointRoot14_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot14Certificate,hc,hp]
end Atlas.ReeF4
