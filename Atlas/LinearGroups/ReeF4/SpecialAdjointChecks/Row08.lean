import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row07

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot7 (x : Fin 26 → F) : F := x 1*x 7 + x 11*x 25 + x 13*x 23 + x 15*x 22 + x 17*x 19
def fullAdjointRoot7Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 6*y 7 + x 7*y 6) + (isotropyCross x y 1) * (x 13*y 15 + x 15*y 13) + (isotropyCross x y 2) * (x 15*y 25 + x 25*y 15) + (isotropyCross x y 3) * (x 13*y 25 + x 25*y 13) + (isotropyCross x y 6) * (x 0*y 7 + x 7*y 0 + x 13*y 23 + x 15*y 22 + x 22*y 15 + x 23*y 13) + (isotropyCross x y 7) * (x 0*y 6 + x 6*y 0 + x 13*y 21 + x 15*y 20 + x 20*y 15 + x 21*y 13) + (isotropyCross x y 8) * (x 15*y 19 + x 19*y 15) + (isotropyCross x y 9) * (x 13*y 19 + x 19*y 13) + (isotropyCross x y 10) * (x 7*y 25 + x 25*y 7) + (isotropyCross x y 11) * (x 6*y 25 + x 25*y 6) + (isotropyCross x y 13) * (x 1*y 15 + x 6*y 23 + x 7*y 21 + x 15*y 1 + x 21*y 7 + x 23*y 6) + (isotropyCross x y 15) * (x 1*y 13 + x 6*y 22 + x 7*y 20 + x 13*y 1 + x 20*y 7 + x 22*y 6) + (isotropyCross x y 16) * (x 7*y 19 + x 19*y 7) + (isotropyCross x y 17) * (x 6*y 19 + x 19*y 6) + (isotropyCross x y 19) * (x 0*y 25 + x 8*y 15 + x 9*y 13 + x 13*y 9 + x 15*y 8 + x 25*y 0) + (isotropyCross x y 20) * (x 7*y 15 + x 15*y 7) + (isotropyCross x y 21) * (x 7*y 13 + x 13*y 7) + (isotropyCross x y 22) * (x 6*y 15 + x 15*y 6) + (isotropyCross x y 23) * (x 6*y 13 + x 13*y 6) + (isotropyCross x y 25) * (x 0*y 19 + x 2*y 15 + x 3*y 13 + x 13*y 3 + x 15*y 2 + x 19*y 0)

theorem fullAdjointRoot7_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 5 = fullAdjointRoot7 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot7,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot7_actual (u : TraceZero F) :
    (adjoint u.val).2 0 5 = fullAdjointRoot7 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot7_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot7_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot7 (isotropyRawStar x y) = fullAdjointRoot7Certificate x y := by
  simp only [fullAdjointRoot7, isotropyRawStar, fullAdjointRoot7Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root7_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 0 5 = 0 := by
  rw [fullAdjointRoot7_actual,isotropyRawStar_actual,fullAdjointRoot7_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot7Certificate,hc,hp]
end Atlas.ReeF4
