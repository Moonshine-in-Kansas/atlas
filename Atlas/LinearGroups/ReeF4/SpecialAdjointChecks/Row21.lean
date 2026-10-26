import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row20

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot20 (x : Fin 26 → F) : F := x 0*x 20 + x 1*x 20 + x 2*x 16 + x 4*x 13 + x 6*x 12 + x 8*x 10
def fullAdjointRoot20Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 3*y 5 + x 5*y 3) + (isotropyCross x y 1) * (x 11*y 14 + x 14*y 11) + (isotropyCross x y 2) * (x 14*y 23 + x 23*y 14) + (isotropyCross x y 3) * (x 0*y 5 + x 5*y 0 + x 11*y 24 + x 14*y 22 + x 22*y 14 + x 24*y 11) + (isotropyCross x y 4) * (x 11*y 23 + x 23*y 11) + (isotropyCross x y 5) * (x 0*y 3 + x 3*y 0 + x 11*y 21 + x 14*y 19 + x 19*y 14 + x 21*y 11) + (isotropyCross x y 7) * (x 14*y 18 + x 18*y 14) + (isotropyCross x y 9) * (x 11*y 18 + x 18*y 11) + (isotropyCross x y 10) * (x 5*y 23 + x 23*y 5) + (isotropyCross x y 11) * (x 1*y 14 + x 3*y 24 + x 5*y 21 + x 14*y 1 + x 21*y 5 + x 24*y 3) + (isotropyCross x y 12) * (x 3*y 23 + x 23*y 3) + (isotropyCross x y 14) * (x 1*y 11 + x 3*y 22 + x 5*y 19 + x 11*y 1 + x 19*y 5 + x 22*y 3) + (isotropyCross x y 15) * (x 5*y 18 + x 18*y 5) + (isotropyCross x y 17) * (x 3*y 18 + x 18*y 3) + (isotropyCross x y 18) * (x 0*y 23 + x 7*y 14 + x 9*y 11 + x 11*y 9 + x 14*y 7 + x 23*y 0) + (isotropyCross x y 19) * (x 5*y 14 + x 14*y 5) + (isotropyCross x y 21) * (x 5*y 11 + x 11*y 5) + (isotropyCross x y 22) * (x 3*y 14 + x 14*y 3) + (isotropyCross x y 23) * (x 0*y 18 + x 2*y 14 + x 4*y 11 + x 11*y 4 + x 14*y 2 + x 18*y 0) + (isotropyCross x y 24) * (x 3*y 11 + x 11*y 3)

theorem fullAdjointRoot20_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 2 = fullAdjointRoot20 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot20,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot20_actual (u : TraceZero F) :
    (adjoint u.val).2 2 2 = fullAdjointRoot20 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot20_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot20_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot20 (isotropyRawStar x y) = fullAdjointRoot20Certificate x y := by
  simp only [fullAdjointRoot20, isotropyRawStar, fullAdjointRoot20Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root20_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 2 = 0 := by
  rw [fullAdjointRoot20_actual,isotropyRawStar_actual,fullAdjointRoot20_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot20Certificate,hc,hp]
end Atlas.ReeF4
