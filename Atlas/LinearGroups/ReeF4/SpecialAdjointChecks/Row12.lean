import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row11

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot11 (x : Fin 26 → F) : F := x 0*x 11 + x 2*x 23 + x 3*x 22 + x 5*x 19 + x 7*x 18
def fullAdjointRoot11Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 2*y 6 + x 6*y 2) + (isotropyCross x y 1) * (x 10*y 13 + x 13*y 10) + (isotropyCross x y 2) * (x 0*y 6 + x 1*y 6 + x 6*y 0 + x 6*y 1 + x 15*y 20 + x 16*y 19 + x 19*y 16 + x 20*y 15) + (isotropyCross x y 3) * (x 13*y 20 + x 20*y 13) + (isotropyCross x y 4) * (x 13*y 19 + x 19*y 13) + (isotropyCross x y 6) * (x 0*y 2 + x 1*y 2 + x 2*y 0 + x 2*y 1 + x 11*y 20 + x 12*y 19 + x 19*y 12 + x 20*y 11) + (isotropyCross x y 7) * (x 10*y 20 + x 20*y 10) + (isotropyCross x y 8) * (x 10*y 19 + x 19*y 10) + (isotropyCross x y 10) * (x 0*y 13 + x 1*y 13 + x 7*y 20 + x 8*y 19 + x 13*y 0 + x 13*y 1 + x 19*y 8 + x 20*y 7) + (isotropyCross x y 11) * (x 6*y 20 + x 20*y 6) + (isotropyCross x y 12) * (x 6*y 19 + x 19*y 6) + (isotropyCross x y 13) * (x 0*y 10 + x 1*y 10 + x 3*y 20 + x 4*y 19 + x 10*y 0 + x 10*y 1 + x 19*y 4 + x 20*y 3) + (isotropyCross x y 15) * (x 2*y 20 + x 20*y 2) + (isotropyCross x y 16) * (x 2*y 19 + x 19*y 2) + (isotropyCross x y 18) * (x 6*y 13 + x 13*y 6) + (isotropyCross x y 19) * (x 0*y 20 + x 4*y 13 + x 8*y 10 + x 10*y 8 + x 13*y 4 + x 20*y 0) + (isotropyCross x y 20) * (x 0*y 19 + x 3*y 13 + x 7*y 10 + x 10*y 7 + x 13*y 3 + x 19*y 0) + (isotropyCross x y 21) * (x 2*y 13 + x 13*y 2) + (isotropyCross x y 22) * (x 6*y 10 + x 10*y 6) + (isotropyCross x y 25) * (x 2*y 10 + x 10*y 2) + (isotropyPolar x y) * (x 2*y 6 + x 6*y 2 + x 10*y 13 + x 13*y 10 + x 19*y 20 + x 20*y 19)

theorem fullAdjointRoot11_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 1 = fullAdjointRoot11 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot11,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot11_actual (u : TraceZero F) :
    (adjoint u.val).2 1 1 = fullAdjointRoot11 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot11_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot11_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot11 (isotropyRawStar x y) = fullAdjointRoot11Certificate x y := by
  simp only [fullAdjointRoot11, isotropyRawStar, fullAdjointRoot11Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root11_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 1 = 0 := by
  rw [fullAdjointRoot11_actual,isotropyRawStar_actual,fullAdjointRoot11_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot11Certificate,hc,hp]
end Atlas.ReeF4
