import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row13

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot13 (x : Fin 26 → F) : F := x 0*x 13 + x 2*x 25 + x 6*x 22 + x 7*x 20 + x 8*x 19
def fullAdjointRoot13Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 11*y 15 + x 15*y 11 + x 19*y 23 + x 23*y 19) + (isotropyCross x y 1) * (x 3*y 7 + x 7*y 3 + x 19*y 23 + x 23*y 19) + (isotropyCross x y 2) * (x 15*y 23 + x 23*y 15) + (isotropyCross x y 3) * (x 0*y 7 + x 7*y 0 + x 11*y 25 + x 15*y 22 + x 22*y 15 + x 25*y 11) + (isotropyCross x y 5) * (x 15*y 19 + x 19*y 15) + (isotropyCross x y 6) * (x 11*y 23 + x 23*y 11) + (isotropyCross x y 7) * (x 0*y 3 + x 3*y 0 + x 11*y 21 + x 15*y 18 + x 18*y 15 + x 21*y 11) + (isotropyCross x y 9) * (x 11*y 19 + x 19*y 11) + (isotropyCross x y 10) * (x 7*y 23 + x 23*y 7) + (isotropyCross x y 11) * (x 1*y 15 + x 3*y 25 + x 7*y 21 + x 15*y 1 + x 21*y 7 + x 25*y 3) + (isotropyCross x y 13) * (x 3*y 23 + x 23*y 3) + (isotropyCross x y 14) * (x 7*y 19 + x 19*y 7) + (isotropyCross x y 15) * (x 1*y 11 + x 3*y 22 + x 7*y 18 + x 11*y 1 + x 18*y 7 + x 22*y 3) + (isotropyCross x y 17) * (x 3*y 19 + x 19*y 3) + (isotropyCross x y 18) * (x 7*y 15 + x 15*y 7) + (isotropyCross x y 19) * (x 0*y 23 + x 5*y 15 + x 9*y 11 + x 11*y 9 + x 15*y 5 + x 23*y 0) + (isotropyCross x y 21) * (x 7*y 11 + x 11*y 7) + (isotropyCross x y 22) * (x 3*y 15 + x 15*y 3) + (isotropyCross x y 23) * (x 0*y 19 + x 2*y 15 + x 6*y 11 + x 11*y 6 + x 15*y 2 + x 19*y 0) + (isotropyCross x y 25) * (x 3*y 11 + x 11*y 3) + (isotropyPolar x y) * (x 3*y 7 + x 7*y 3 + x 11*y 15 + x 15*y 11 + x 19*y 23 + x 23*y 19)

theorem fullAdjointRoot13_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 3 = fullAdjointRoot13 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot13,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot13_actual (u : TraceZero F) :
    (adjoint u.val).2 1 3 = fullAdjointRoot13 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot13_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot13_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot13 (isotropyRawStar x y) = fullAdjointRoot13Certificate x y := by
  simp only [fullAdjointRoot13, isotropyRawStar, fullAdjointRoot13Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root13_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 3 = 0 := by
  rw [fullAdjointRoot13_actual,isotropyRawStar_actual,fullAdjointRoot13_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot13Certificate,hc,hp]
end Atlas.ReeF4
