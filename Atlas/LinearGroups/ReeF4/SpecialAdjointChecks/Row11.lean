import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row10

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot10 (x : Fin 26 → F) : F := x 0*x 10 + x 2*x 21 + x 3*x 20 + x 4*x 19 + x 6*x 18
def fullAdjointRoot10Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 2*y 5 + x 5*y 2) + (isotropyCross x y 1) * (x 2*y 5 + x 5*y 2 + x 18*y 22 + x 22*y 18) + (isotropyCross x y 2) * (x 0*y 5 + x 5*y 0 + x 11*y 24 + x 12*y 23 + x 23*y 12 + x 24*y 11) + (isotropyCross x y 3) * (x 12*y 22 + x 22*y 12) + (isotropyCross x y 4) * (x 11*y 22 + x 22*y 11) + (isotropyCross x y 5) * (x 0*y 2 + x 2*y 0 + x 11*y 20 + x 12*y 19 + x 19*y 12 + x 20*y 11) + (isotropyCross x y 7) * (x 12*y 18 + x 18*y 12) + (isotropyCross x y 8) * (x 11*y 18 + x 18*y 11) + (isotropyCross x y 10) * (x 5*y 22 + x 22*y 5) + (isotropyCross x y 11) * (x 0*y 12 + x 1*y 12 + x 4*y 22 + x 8*y 18 + x 12*y 0 + x 12*y 1 + x 18*y 8 + x 22*y 4) + (isotropyCross x y 12) * (x 0*y 11 + x 1*y 11 + x 3*y 22 + x 7*y 18 + x 11*y 0 + x 11*y 1 + x 18*y 7 + x 22*y 3) + (isotropyCross x y 13) * (x 5*y 18 + x 18*y 5) + (isotropyCross x y 14) * (x 2*y 22 + x 22*y 2) + (isotropyCross x y 17) * (x 2*y 18 + x 18*y 2) + (isotropyCross x y 18) * (x 0*y 22 + x 7*y 12 + x 8*y 11 + x 11*y 8 + x 12*y 7 + x 22*y 0) + (isotropyCross x y 19) * (x 5*y 12 + x 12*y 5) + (isotropyCross x y 20) * (x 5*y 11 + x 11*y 5) + (isotropyCross x y 22) * (x 0*y 18 + x 3*y 12 + x 4*y 11 + x 11*y 4 + x 12*y 3 + x 18*y 0) + (isotropyCross x y 23) * (x 2*y 12 + x 12*y 2) + (isotropyCross x y 24) * (x 2*y 11 + x 11*y 2) + (isotropyPolar x y) * (x 2*y 5 + x 5*y 2 + x 11*y 12 + x 12*y 11 + x 18*y 22 + x 22*y 18)

theorem fullAdjointRoot10_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 0 = fullAdjointRoot10 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot10,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot10_actual (u : TraceZero F) :
    (adjoint u.val).2 1 0 = fullAdjointRoot10 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot10_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot10_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot10 (isotropyRawStar x y) = fullAdjointRoot10Certificate x y := by
  simp only [fullAdjointRoot10, isotropyRawStar, fullAdjointRoot10Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root10_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 1 0 = 0 := by
  rw [fullAdjointRoot10_actual,isotropyRawStar_actual,fullAdjointRoot10_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot10Certificate,hc,hp]
end Atlas.ReeF4
