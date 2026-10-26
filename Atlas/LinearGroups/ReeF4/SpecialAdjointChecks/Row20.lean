import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row19

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot19 (x : Fin 26 → F) : F := x 0*x 19 + x 1*x 19 + x 2*x 15 + x 3*x 13 + x 6*x 11 + x 7*x 10
def fullAdjointRoot19Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 11*y 13 + x 13*y 11 + x 19*y 22 + x 22*y 19) + (isotropyCross x y 1) * (x 11*y 13 + x 13*y 11) + (isotropyCross x y 2) * (x 0*y 7 + x 7*y 0 + x 11*y 25 + x 13*y 23 + x 23*y 13 + x 25*y 11) + (isotropyCross x y 3) * (x 13*y 22 + x 22*y 13) + (isotropyCross x y 5) * (x 13*y 19 + x 19*y 13) + (isotropyCross x y 6) * (x 11*y 22 + x 22*y 11) + (isotropyCross x y 7) * (x 0*y 2 + x 2*y 0 + x 11*y 20 + x 13*y 18 + x 18*y 13 + x 20*y 11) + (isotropyCross x y 8) * (x 11*y 19 + x 19*y 11) + (isotropyCross x y 10) * (x 7*y 22 + x 22*y 7) + (isotropyCross x y 11) * (x 0*y 13 + x 1*y 13 + x 6*y 22 + x 8*y 19 + x 13*y 0 + x 13*y 1 + x 19*y 8 + x 22*y 6) + (isotropyCross x y 12) * (x 7*y 19 + x 19*y 7) + (isotropyCross x y 13) * (x 0*y 11 + x 1*y 11 + x 3*y 22 + x 5*y 19 + x 11*y 0 + x 11*y 1 + x 19*y 5 + x 22*y 3) + (isotropyCross x y 15) * (x 2*y 22 + x 22*y 2) + (isotropyCross x y 17) * (x 2*y 19 + x 19*y 2) + (isotropyCross x y 18) * (x 7*y 13 + x 13*y 7) + (isotropyCross x y 19) * (x 0*y 22 + x 5*y 13 + x 8*y 11 + x 11*y 8 + x 13*y 5 + x 22*y 0) + (isotropyCross x y 20) * (x 7*y 11 + x 11*y 7) + (isotropyCross x y 22) * (x 0*y 19 + x 3*y 13 + x 6*y 11 + x 11*y 6 + x 13*y 3 + x 19*y 0) + (isotropyCross x y 23) * (x 2*y 13 + x 13*y 2) + (isotropyCross x y 25) * (x 2*y 11 + x 11*y 2)

theorem fullAdjointRoot19_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 1 = fullAdjointRoot19 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot19,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot19_actual (u : TraceZero F) :
    (adjoint u.val).2 2 1 = fullAdjointRoot19 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot19_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot19_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot19 (isotropyRawStar x y) = fullAdjointRoot19Certificate x y := by
  simp only [fullAdjointRoot19, isotropyRawStar, fullAdjointRoot19Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root19_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 1 = 0 := by
  rw [fullAdjointRoot19_actual,isotropyRawStar_actual,fullAdjointRoot19_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot19Certificate,hc,hp]
end Atlas.ReeF4
