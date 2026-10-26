import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row25

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
def fullAdjointRoot25 (x : Fin 26 → F) : F := x 0*x 25 + x 1*x 25 + x 6*x 17 + x 7*x 16 + x 8*x 15 + x 9*x 13
def fullAdjointRoot25Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 15*y 17 + x 17*y 15 + x 23*y 25 + x 25*y 23) + (isotropyCross x y 1) * (x 7*y 9 + x 9*y 7 + x 23*y 25 + x 25*y 23) + (isotropyCross x y 3) * (x 17*y 25 + x 25*y 17) + (isotropyCross x y 5) * (x 15*y 25 + x 25*y 15) + (isotropyCross x y 6) * (x 17*y 23 + x 23*y 17) + (isotropyCross x y 7) * (x 0*y 9 + x 9*y 0 + x 15*y 24 + x 17*y 21 + x 21*y 17 + x 24*y 15) + (isotropyCross x y 8) * (x 15*y 23 + x 23*y 15) + (isotropyCross x y 9) * (x 0*y 7 + x 7*y 0 + x 15*y 22 + x 17*y 19 + x 19*y 17 + x 22*y 15) + (isotropyCross x y 11) * (x 9*y 25 + x 25*y 9) + (isotropyCross x y 13) * (x 9*y 23 + x 23*y 9) + (isotropyCross x y 14) * (x 7*y 25 + x 25*y 7) + (isotropyCross x y 15) * (x 1*y 17 + x 7*y 24 + x 9*y 22 + x 17*y 1 + x 22*y 9 + x 24*y 7) + (isotropyCross x y 16) * (x 7*y 23 + x 23*y 7) + (isotropyCross x y 17) * (x 1*y 15 + x 7*y 21 + x 9*y 19 + x 15*y 1 + x 19*y 9 + x 21*y 7) + (isotropyCross x y 19) * (x 9*y 17 + x 17*y 9) + (isotropyCross x y 21) * (x 7*y 17 + x 17*y 7) + (isotropyCross x y 22) * (x 9*y 15 + x 15*y 9) + (isotropyCross x y 23) * (x 0*y 25 + x 6*y 17 + x 8*y 15 + x 15*y 8 + x 17*y 6 + x 25*y 0) + (isotropyCross x y 24) * (x 7*y 15 + x 15*y 7) + (isotropyCross x y 25) * (x 0*y 23 + x 3*y 17 + x 5*y 15 + x 15*y 5 + x 17*y 3 + x 23*y 0)

theorem fullAdjointRoot25_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 2 7 = fullAdjointRoot25 x := by
  simp [adjoint,isotropyPoint,fullAdjointRoot25,SplitOctonion.mul,SplitOctonion.norm,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem fullAdjointRoot25_actual (u : TraceZero F) :
    (adjoint u.val).2 2 7 = fullAdjointRoot25 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using fullAdjointRoot25_point (isotropyCoordinates u)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem fullAdjointRoot25_quartic_identity (x y : Fin 26 → F) :
    fullAdjointRoot25 (isotropyRawStar x y) = fullAdjointRoot25Certificate x y := by
  simp only [fullAdjointRoot25, isotropyRawStar, fullAdjointRoot25Certificate, isotropyCross, isotropyPolar, Matrix.cons_val, CharTwo.add_sq, mul_pow]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem rawStar_adjoint_root25_zero (u v : TraceZero F) (h : StarDomain u v) :
    (adjoint (proposedStarLinear (wedge u v)).val).2 2 7 = 0 := by
  rw [fullAdjointRoot25_actual,isotropyRawStar_actual,fullAdjointRoot25_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [fullAdjointRoot25Certificate,hc,hp]
end Atlas.ReeF4
