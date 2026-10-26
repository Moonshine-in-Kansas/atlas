import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row23

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot23 (x : Fin 26 → F) : F := x 0*x 23 + x 1*x 23 + x 3*x 17 + x 5*x 15 + x 7*x 14 + x 9*x 11
def fullAdjointRoot23Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 6*y 8 + x 8*y 6) + (isotropyCross x y 1) * (x 13*y 16 + x 16*y 13) + (isotropyCross x y 2) * (x 16*y 25 + x 25*y 16) + (isotropyCross x y 4) * (x 13*y 25 + x 25*y 13) + (isotropyCross x y 6) * (x 0*y 8 + x 8*y 0 + x 13*y 24 + x 16*y 22 + x 22*y 16 + x 24*y 13) + (isotropyCross x y 7) * (x 16*y 20 + x 20*y 16) + (isotropyCross x y 8) * (x 0*y 6 + x 6*y 0 + x 13*y 21 + x 16*y 19 + x 19*y 16 + x 21*y 13) + (isotropyCross x y 9) * (x 13*y 20 + x 20*y 13) + (isotropyCross x y 10) * (x 8*y 25 + x 25*y 8) + (isotropyCross x y 12) * (x 6*y 25 + x 25*y 6) + (isotropyCross x y 13) * (x 1*y 16 + x 6*y 24 + x 8*y 21 + x 16*y 1 + x 21*y 8 + x 24*y 6) + (isotropyCross x y 15) * (x 8*y 20 + x 20*y 8) + (isotropyCross x y 16) * (x 1*y 13 + x 6*y 22 + x 8*y 19 + x 13*y 1 + x 19*y 8 + x 22*y 6) + (isotropyCross x y 17) * (x 6*y 20 + x 20*y 6) + (isotropyCross x y 19) * (x 8*y 16 + x 16*y 8) + (isotropyCross x y 20) * (x 0*y 25 + x 7*y 16 + x 9*y 13 + x 13*y 9 + x 16*y 7 + x 25*y 0) + (isotropyCross x y 21) * (x 8*y 13 + x 13*y 8) + (isotropyCross x y 22) * (x 6*y 16 + x 16*y 6) + (isotropyCross x y 24) * (x 6*y 13 + x 13*y 6) + (isotropyCross x y 25) * (x 0*y 20 + x 2*y 16 + x 4*y 13 + x 13*y 4 + x 16*y 2 + x 20*y 0)

theorem fullAdjointRoot23_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 5 = fullAdjointRoot23 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot23,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot23_actual (u : TraceZero F) :
    (adjoint u.val).2 2 5 = fullAdjointRoot23 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot23_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot23_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot23 (isotropyRawStar x y) = fullAdjointRoot23Certificate x y := by
  simp only [fullAdjointRoot23, isotropyRawStar, fullAdjointRoot23Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root23_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 5 = 0 := by
  rw [fullAdjointRoot23_actual,isotropyRawStar_actual,fullAdjointRoot23_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot23Certificate,hc,hp]
end Atlas.ReeF4
