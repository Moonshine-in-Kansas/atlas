import Atlas.LinearGroups.ReeF4.SpecialIsotropyFormulas

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialAdjoint9 (x : Fin 26 → F) : F := x 1*x 9+x 14*x 25+x 15*x 24+x 16*x 23+x 17*x 21

def specialAdjoint9Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 16*y 17 + x 17*y 16 + x 24*y 25 + x 25*y 24) + (isotropyCross x y 1) * (x 8*y 9 + x 9*y 8 + x 24*y 25 + x 25*y 24) + (isotropyCross x y 4) * (x 17*y 25 + x 25*y 17) + (isotropyCross x y 5) * (x 16*y 25 + x 25*y 16) + (isotropyCross x y 6) * (x 17*y 24 + x 24*y 17) + (isotropyCross x y 7) * (x 16*y 24 + x 24*y 16) + (isotropyCross x y 8) * (x 0*y 9 + x 9*y 0 + x 16*y 23 + x 17*y 21 + x 21*y 17 + x 23*y 16) + (isotropyCross x y 9) * (x 0*y 8 + x 8*y 0 + x 16*y 22 + x 17*y 20 + x 20*y 17 + x 22*y 16) + (isotropyCross x y 12) * (x 9*y 25 + x 25*y 9) + (isotropyCross x y 13) * (x 9*y 24 + x 24*y 9) + (isotropyCross x y 14) * (x 8*y 25 + x 25*y 8) + (isotropyCross x y 15) * (x 8*y 24 + x 24*y 8) + (isotropyCross x y 16) * (x 1*y 17 + x 8*y 23 + x 9*y 22 + x 17*y 1 + x 22*y 9 + x 23*y 8) + (isotropyCross x y 17) * (x 1*y 16 + x 8*y 21 + x 9*y 20 + x 16*y 1 + x 20*y 9 + x 21*y 8) + (isotropyCross x y 20) * (x 9*y 17 + x 17*y 9) + (isotropyCross x y 21) * (x 8*y 17 + x 17*y 8) + (isotropyCross x y 22) * (x 9*y 16 + x 16*y 9) + (isotropyCross x y 23) * (x 8*y 16 + x 16*y 8) + (isotropyCross x y 24) * (x 0*y 25 + x 6*y 17 + x 7*y 16 + x 16*y 7 + x 17*y 6 + x 25*y 0) + (isotropyCross x y 25) * (x 0*y 24 + x 4*y 17 + x 5*y 16 + x 16*y 5 + x 17*y 4 + x 24*y 0)
theorem specialAdjoint9_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 0 7 = specialAdjoint9 x := by
  simp [adjoint,isotropyPoint,specialAdjoint9,SplitOctonion.mul,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem specialAdjoint9_actual (u : TraceZero F) :
    (adjoint u.val).2 0 7 = specialAdjoint9 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using specialAdjoint9_point (isotropyCoordinates u)

theorem specialAdjoint9_map {R : Type*} [CommRing R] [CharP R 2]
    (σ : F →+* R) (x : Fin 26 → F) :
    specialAdjoint9 (fun j => σ (x j)) = σ (specialAdjoint9 x) := by
  simp only [specialAdjoint9,_root_.map_add,_root_.map_mul]

def specialAdjoint17 (x : Fin 26 → F) : F := x 0*x 17+x 5*x 25+x 7*x 24+x 8*x 23+x 9*x 22

def specialAdjoint17Certificate (x y : Fin 26 → F) : F := (isotropyCross x y 0) * (x 6*y 9 + x 9*y 6) + (isotropyCross x y 1) * (x 6*y 9 + x 9*y 6 + x 21*y 25 + x 25*y 21) + (isotropyCross x y 3) * (x 16*y 25 + x 25*y 16) + (isotropyCross x y 4) * (x 15*y 25 + x 25*y 15) + (isotropyCross x y 6) * (x 0*y 9 + x 9*y 0 + x 15*y 24 + x 16*y 23 + x 23*y 16 + x 24*y 15) + (isotropyCross x y 7) * (x 16*y 21 + x 21*y 16) + (isotropyCross x y 8) * (x 15*y 21 + x 21*y 15) + (isotropyCross x y 9) * (x 0*y 6 + x 6*y 0 + x 15*y 20 + x 16*y 19 + x 19*y 16 + x 20*y 15) + (isotropyCross x y 10) * (x 9*y 25 + x 25*y 9) + (isotropyCross x y 13) * (x 9*y 21 + x 21*y 9) + (isotropyCross x y 14) * (x 6*y 25 + x 25*y 6) + (isotropyCross x y 15) * (x 1*y 16 + x 6*y 24 + x 9*y 20 + x 16*y 1 + x 20*y 9 + x 24*y 6) + (isotropyCross x y 16) * (x 1*y 15 + x 6*y 23 + x 9*y 19 + x 15*y 1 + x 19*y 9 + x 23*y 6) + (isotropyCross x y 17) * (x 6*y 21 + x 21*y 6) + (isotropyCross x y 19) * (x 9*y 16 + x 16*y 9) + (isotropyCross x y 20) * (x 9*y 15 + x 15*y 9) + (isotropyCross x y 21) * (x 0*y 25 + x 7*y 16 + x 8*y 15 + x 15*y 8 + x 16*y 7 + x 25*y 0) + (isotropyCross x y 23) * (x 6*y 16 + x 16*y 6) + (isotropyCross x y 24) * (x 6*y 15 + x 15*y 6) + (isotropyCross x y 25) * (x 0*y 21 + x 3*y 16 + x 4*y 15 + x 15*y 4 + x 16*y 3 + x 21*y 0) + (isotropyPolar x y) * (x 6*y 9 + x 9*y 6 + x 15*y 16 + x 16*y 15 + x 21*y 25 + x 25*y 21)
theorem specialAdjoint17_point (x : Fin 26 → F) :
    (adjoint (isotropyPoint x).val).2 1 7 = specialAdjoint17 x := by
  simp [adjoint,isotropyPoint,specialAdjoint17,SplitOctonion.mul,
    SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,CharTwo.neg_eq]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

theorem specialAdjoint17_actual (u : TraceZero F) :
    (adjoint u.val).2 1 7 = specialAdjoint17 (isotropyCoordinates u) := by
  simpa only [isotropyPoint_coordinates] using specialAdjoint17_point (isotropyCoordinates u)

theorem specialAdjoint17_map {R : Type*} [CommRing R] [CharP R 2]
    (σ : F →+* R) (x : Fin 26 → F) :
    specialAdjoint17 (fun j => σ (x j)) = σ (specialAdjoint17 x) := by
  simp only [specialAdjoint17,_root_.map_add,_root_.map_mul]

end Atlas.ReeF4
