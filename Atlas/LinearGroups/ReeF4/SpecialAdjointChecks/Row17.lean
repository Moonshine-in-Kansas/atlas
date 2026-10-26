import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row16

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot16 (x : Fin 26 → F) : F := x 0*x 16 + x 4*x 25 + x 6*x 24 + x 8*x 21 + x 9*x 20
def fullAdjointRoot16Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 5*y 9 + x 9*y 5) + (isotropyCross x y 1) * (x 14*y 17 + x 17*y 14) + (isotropyCross x y 3) * (x 17*y 24 + x 24*y 17) + (isotropyCross x y 4) * (x 17*y 23 + x 23*y 17) + (isotropyCross x y 5) * (x 0*y 9 + x 9*y 0 + x 14*y 25 + x 17*y 21 + x 21*y 17 + x 25*y 14) + (isotropyCross x y 7) * (x 14*y 24 + x 24*y 14) + (isotropyCross x y 8) * (x 14*y 23 + x 23*y 14) + (isotropyCross x y 9) * (x 0*y 5 + x 5*y 0 + x 14*y 22 + x 17*y 18 + x 18*y 17 + x 22*y 14) + (isotropyCross x y 11) * (x 9*y 24 + x 24*y 9) + (isotropyCross x y 12) * (x 9*y 23 + x 23*y 9) + (isotropyCross x y 14) * (x 1*y 17 + x 5*y 25 + x 9*y 22 + x 17*y 1 + x 22*y 9 + x 25*y 5) + (isotropyCross x y 15) * (x 5*y 24 + x 24*y 5) + (isotropyCross x y 16) * (x 5*y 23 + x 23*y 5) + (isotropyCross x y 17) * (x 1*y 14 + x 5*y 21 + x 9*y 18 + x 14*y 1 + x 18*y 9 + x 21*y 5) + (isotropyCross x y 18) * (x 9*y 17 + x 17*y 9) + (isotropyCross x y 21) * (x 5*y 17 + x 17*y 5) + (isotropyCross x y 22) * (x 9*y 14 + x 14*y 9) + (isotropyCross x y 23) * (x 0*y 24 + x 4*y 17 + x 8*y 14 + x 14*y 8 + x 17*y 4 + x 24*y 0) + (isotropyCross x y 24) * (x 0*y 23 + x 3*y 17 + x 7*y 14 + x 14*y 7 + x 17*y 3 + x 23*y 0) + (isotropyCross x y 25) * (x 5*y 14 + x 14*y 5) + (isotropyPolar x y) * (x 5*y 9 + x 9*y 5 + x 14*y 17 + x 17*y 14 + x 23*y 24 + x 24*y 23)

theorem fullAdjointRoot16_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 6 = fullAdjointRoot16 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot16,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot16_actual (u : TraceZero F) :
    (adjoint u.val).2 1 6 = fullAdjointRoot16 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot16_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot16_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot16 (isotropyRawStar x y) = fullAdjointRoot16Certificate x y := by
  simp only [fullAdjointRoot16, isotropyRawStar, fullAdjointRoot16Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root16_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 6 = 0 := by
  rw [fullAdjointRoot16_actual,isotropyRawStar_actual,fullAdjointRoot16_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot16Certificate,hc,hp]
end Atlas.ReeF4
