import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row15

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot15 (x : Fin 26 → F) : F := x 0*x 15 + x 3*x 25 + x 6*x 23 + x 7*x 21 + x 9*x 19
def fullAdjointRoot15Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 13*y 17 + x 17*y 13 + x 22*y 25 + x 25*y 22) + (isotropyCross x y 1) * (x 13*y 17 + x 17*y 13) + (isotropyCross x y 2) * (x 17*y 25 + x 25*y 17) + (isotropyCross x y 5) * (x 13*y 25 + x 25*y 13) + (isotropyCross x y 6) * (x 17*y 22 + x 22*y 17) + (isotropyCross x y 7) * (x 0*y 8 + x 8*y 0 + x 13*y 24 + x 17*y 20 + x 20*y 17 + x 24*y 13) + (isotropyCross x y 8) * (x 0*y 7 + x 7*y 0 + x 13*y 23 + x 17*y 19 + x 19*y 17 + x 23*y 13) + (isotropyCross x y 9) * (x 13*y 22 + x 22*y 13) + (isotropyCross x y 11) * (x 8*y 25 + x 25*y 8) + (isotropyCross x y 12) * (x 7*y 25 + x 25*y 7) + (isotropyCross x y 13) * (x 1*y 17 + x 7*y 24 + x 8*y 23 + x 17*y 1 + x 23*y 8 + x 24*y 7) + (isotropyCross x y 15) * (x 8*y 22 + x 22*y 8) + (isotropyCross x y 16) * (x 7*y 22 + x 22*y 7) + (isotropyCross x y 17) * (x 1*y 13 + x 7*y 20 + x 8*y 19 + x 13*y 1 + x 19*y 8 + x 20*y 7) + (isotropyCross x y 19) * (x 8*y 17 + x 17*y 8) + (isotropyCross x y 20) * (x 7*y 17 + x 17*y 7) + (isotropyCross x y 22) * (x 0*y 25 + x 6*y 17 + x 9*y 13 + x 13*y 9 + x 17*y 6 + x 25*y 0) + (isotropyCross x y 23) * (x 8*y 13 + x 13*y 8) + (isotropyCross x y 24) * (x 7*y 13 + x 13*y 7) + (isotropyCross x y 25) * (x 0*y 22 + x 2*y 17 + x 5*y 13 + x 13*y 5 + x 17*y 2 + x 22*y 0) + (isotropyPolar x y) * (x 7*y 8 + x 8*y 7 + x 13*y 17 + x 17*y 13 + x 22*y 25 + x 25*y 22)

theorem fullAdjointRoot15_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 5 = fullAdjointRoot15 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot15,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot15_actual (u : TraceZero F) :
    (adjoint u.val).2 1 5 = fullAdjointRoot15 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot15_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot15_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot15 (isotropyRawStar x y) = fullAdjointRoot15Certificate x y := by
  simp only [fullAdjointRoot15, isotropyRawStar, fullAdjointRoot15Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root15_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 5 = 0 := by
  rw [fullAdjointRoot15_actual,isotropyRawStar_actual,fullAdjointRoot15_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot15Certificate,hc,hp]
end Atlas.ReeF4
