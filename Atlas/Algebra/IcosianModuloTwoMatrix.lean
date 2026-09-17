import Atlas.Algebra.GoldenModuloTwo
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.CharP.Two

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra

abbrev IcosianMatrix := Matrix (Fin 2) (Fin 2) GoldenFour

def icosianMatrixFromCoefficients (a : Fin 4 → GoldenFour) : IcosianMatrix :=
  !![a 0+a 1+goldenFourTau*a 3, a 1+(goldenFourTau+1)*a 2+goldenFourTau*a 3;
     goldenFourTau*(a 2+a 3), a 0+a 1+a 2+a 3]

def icosianMatrixCoefficients (m : IcosianMatrix) : Fin 4 → GoldenFour :=
  let d := (goldenFourTau+1)*(m 1 1+m 0 0)+goldenFourTau*m 1 0
  let c := (goldenFourTau+1)*(m 1 1+m 0 0)+m 1 0
  let b := m 0 1+(goldenFourTau+1)*c+goldenFourTau*d
  ![m 0 0+b+goldenFourTau*d,b,c,d]

theorem icosianMatrixFromCoefficients_mul (a b : Fin 4 → GoldenFour) :
    icosianMatrixFromCoefficients (icosianCoefficientProduct goldenFourTau a b)=
      icosianMatrixFromCoefficients a*icosianMatrixFromCoefficients b := by
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianCoefficientProduct,Matrix.mul_apply,
      Fin.sum_univ_two,goldenFourTau,QuadraticAlgebra.omega] <;> (try simp only [CharTwo.sub_eq_add, CharTwo.neg_eq]) <;> ring_nf <;> simp only [(show (2 : ZMod 2)=0 from rfl), (show (3 : ZMod 2)=1 from rfl), (show (4 : ZMod 2)=0 from rfl), (show (5 : ZMod 2)=1 from rfl), (show (6 : ZMod 2)=0 from rfl), (show (7 : ZMod 2)=1 from rfl), (show (8 : ZMod 2)=0 from rfl), (show (9 : ZMod 2)=1 from rfl), (show (10 : ZMod 2)=0 from rfl), (show (11 : ZMod 2)=1 from rfl), (show (12 : ZMod 2)=0 from rfl), (show (13 : ZMod 2)=1 from rfl), (show (14 : ZMod 2)=0 from rfl), (show (15 : ZMod 2)=1 from rfl), (show (16 : ZMod 2)=0 from rfl), (show (17 : ZMod 2)=1 from rfl), (show (18 : ZMod 2)=0 from rfl), (show (19 : ZMod 2)=1 from rfl), (show (20 : ZMod 2)=0 from rfl), (show (21 : ZMod 2)=1 from rfl), (show (22 : ZMod 2)=0 from rfl), (show (23 : ZMod 2)=1 from rfl), (show (24 : ZMod 2)=0 from rfl), (show (25 : ZMod 2)=1 from rfl), (show (26 : ZMod 2)=0 from rfl), (show (27 : ZMod 2)=1 from rfl), (show (28 : ZMod 2)=0 from rfl), (show (29 : ZMod 2)=1 from rfl), (show (30 : ZMod 2)=0 from rfl), (show (31 : ZMod 2)=1 from rfl), (show (32 : ZMod 2)=0 from rfl), (show (33 : ZMod 2)=1 from rfl), (show (34 : ZMod 2)=0 from rfl), (show (35 : ZMod 2)=1 from rfl), (show (36 : ZMod 2)=0 from rfl), (show (37 : ZMod 2)=1 from rfl), (show (38 : ZMod 2)=0 from rfl), (show (39 : ZMod 2)=1 from rfl), (show (40 : ZMod 2)=0 from rfl), (show (41 : ZMod 2)=1 from rfl), (show (42 : ZMod 2)=0 from rfl), (show (43 : ZMod 2)=1 from rfl), (show (44 : ZMod 2)=0 from rfl), (show (45 : ZMod 2)=1 from rfl), (show (46 : ZMod 2)=0 from rfl), (show (47 : ZMod 2)=1 from rfl), (show (48 : ZMod 2)=0 from rfl), (show (49 : ZMod 2)=1 from rfl), (show (50 : ZMod 2)=0 from rfl), (show (51 : ZMod 2)=1 from rfl), (show (52 : ZMod 2)=0 from rfl), (show (53 : ZMod 2)=1 from rfl), (show (54 : ZMod 2)=0 from rfl), (show (55 : ZMod 2)=1 from rfl), (show (56 : ZMod 2)=0 from rfl), (show (57 : ZMod 2)=1 from rfl), (show (58 : ZMod 2)=0 from rfl), (show (59 : ZMod 2)=1 from rfl), (show (60 : ZMod 2)=0 from rfl), (show (61 : ZMod 2)=1 from rfl), (show (62 : ZMod 2)=0 from rfl), (show (63 : ZMod 2)=1 from rfl), (show (64 : ZMod 2)=0 from rfl), mul_zero, mul_one, add_zero, zero_add, sub_zero] <;> ring

theorem icosianMatrixFromCoefficients_inverse (m : IcosianMatrix) :
    icosianMatrixFromCoefficients (icosianMatrixCoefficients m)=m := by
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianMatrixCoefficients,
      goldenFourTau,QuadraticAlgebra.omega] <;> (try simp only [CharTwo.sub_eq_add, CharTwo.neg_eq]) <;> ring_nf <;> simp only [(show (2 : ZMod 2)=0 from rfl), (show (3 : ZMod 2)=1 from rfl), (show (4 : ZMod 2)=0 from rfl), (show (5 : ZMod 2)=1 from rfl), (show (6 : ZMod 2)=0 from rfl), (show (7 : ZMod 2)=1 from rfl), (show (8 : ZMod 2)=0 from rfl), (show (9 : ZMod 2)=1 from rfl), (show (10 : ZMod 2)=0 from rfl), (show (11 : ZMod 2)=1 from rfl), (show (12 : ZMod 2)=0 from rfl), (show (13 : ZMod 2)=1 from rfl), (show (14 : ZMod 2)=0 from rfl), (show (15 : ZMod 2)=1 from rfl), (show (16 : ZMod 2)=0 from rfl), (show (17 : ZMod 2)=1 from rfl), (show (18 : ZMod 2)=0 from rfl), (show (19 : ZMod 2)=1 from rfl), (show (20 : ZMod 2)=0 from rfl), (show (21 : ZMod 2)=1 from rfl), (show (22 : ZMod 2)=0 from rfl), (show (23 : ZMod 2)=1 from rfl), (show (24 : ZMod 2)=0 from rfl), (show (25 : ZMod 2)=1 from rfl), (show (26 : ZMod 2)=0 from rfl), (show (27 : ZMod 2)=1 from rfl), (show (28 : ZMod 2)=0 from rfl), (show (29 : ZMod 2)=1 from rfl), (show (30 : ZMod 2)=0 from rfl), (show (31 : ZMod 2)=1 from rfl), (show (32 : ZMod 2)=0 from rfl), (show (33 : ZMod 2)=1 from rfl), (show (34 : ZMod 2)=0 from rfl), (show (35 : ZMod 2)=1 from rfl), (show (36 : ZMod 2)=0 from rfl), (show (37 : ZMod 2)=1 from rfl), (show (38 : ZMod 2)=0 from rfl), (show (39 : ZMod 2)=1 from rfl), (show (40 : ZMod 2)=0 from rfl), (show (41 : ZMod 2)=1 from rfl), (show (42 : ZMod 2)=0 from rfl), (show (43 : ZMod 2)=1 from rfl), (show (44 : ZMod 2)=0 from rfl), (show (45 : ZMod 2)=1 from rfl), (show (46 : ZMod 2)=0 from rfl), (show (47 : ZMod 2)=1 from rfl), (show (48 : ZMod 2)=0 from rfl), (show (49 : ZMod 2)=1 from rfl), (show (50 : ZMod 2)=0 from rfl), (show (51 : ZMod 2)=1 from rfl), (show (52 : ZMod 2)=0 from rfl), (show (53 : ZMod 2)=1 from rfl), (show (54 : ZMod 2)=0 from rfl), (show (55 : ZMod 2)=1 from rfl), (show (56 : ZMod 2)=0 from rfl), (show (57 : ZMod 2)=1 from rfl), (show (58 : ZMod 2)=0 from rfl), (show (59 : ZMod 2)=1 from rfl), (show (60 : ZMod 2)=0 from rfl), (show (61 : ZMod 2)=1 from rfl), (show (62 : ZMod 2)=0 from rfl), (show (63 : ZMod 2)=1 from rfl), (show (64 : ZMod 2)=0 from rfl), mul_zero, mul_one, add_zero, zero_add, sub_zero] <;> ring

theorem icosianMatrixCoefficients_inverse (a : Fin 4 → GoldenFour) :
    icosianMatrixCoefficients (icosianMatrixFromCoefficients a)=a := by
  funext i
  fin_cases i <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianMatrixCoefficients,
      goldenFourTau,QuadraticAlgebra.omega] <;> (try simp only [CharTwo.sub_eq_add, CharTwo.neg_eq]) <;> ring_nf <;> simp only [(show (2 : ZMod 2)=0 from rfl), (show (3 : ZMod 2)=1 from rfl), (show (4 : ZMod 2)=0 from rfl), (show (5 : ZMod 2)=1 from rfl), (show (6 : ZMod 2)=0 from rfl), (show (7 : ZMod 2)=1 from rfl), (show (8 : ZMod 2)=0 from rfl), (show (9 : ZMod 2)=1 from rfl), (show (10 : ZMod 2)=0 from rfl), (show (11 : ZMod 2)=1 from rfl), (show (12 : ZMod 2)=0 from rfl), (show (13 : ZMod 2)=1 from rfl), (show (14 : ZMod 2)=0 from rfl), (show (15 : ZMod 2)=1 from rfl), (show (16 : ZMod 2)=0 from rfl), (show (17 : ZMod 2)=1 from rfl), (show (18 : ZMod 2)=0 from rfl), (show (19 : ZMod 2)=1 from rfl), (show (20 : ZMod 2)=0 from rfl), (show (21 : ZMod 2)=1 from rfl), (show (22 : ZMod 2)=0 from rfl), (show (23 : ZMod 2)=1 from rfl), (show (24 : ZMod 2)=0 from rfl), (show (25 : ZMod 2)=1 from rfl), (show (26 : ZMod 2)=0 from rfl), (show (27 : ZMod 2)=1 from rfl), (show (28 : ZMod 2)=0 from rfl), (show (29 : ZMod 2)=1 from rfl), (show (30 : ZMod 2)=0 from rfl), (show (31 : ZMod 2)=1 from rfl), (show (32 : ZMod 2)=0 from rfl), (show (33 : ZMod 2)=1 from rfl), (show (34 : ZMod 2)=0 from rfl), (show (35 : ZMod 2)=1 from rfl), (show (36 : ZMod 2)=0 from rfl), (show (37 : ZMod 2)=1 from rfl), (show (38 : ZMod 2)=0 from rfl), (show (39 : ZMod 2)=1 from rfl), (show (40 : ZMod 2)=0 from rfl), (show (41 : ZMod 2)=1 from rfl), (show (42 : ZMod 2)=0 from rfl), (show (43 : ZMod 2)=1 from rfl), (show (44 : ZMod 2)=0 from rfl), (show (45 : ZMod 2)=1 from rfl), (show (46 : ZMod 2)=0 from rfl), (show (47 : ZMod 2)=1 from rfl), (show (48 : ZMod 2)=0 from rfl), (show (49 : ZMod 2)=1 from rfl), (show (50 : ZMod 2)=0 from rfl), (show (51 : ZMod 2)=1 from rfl), (show (52 : ZMod 2)=0 from rfl), (show (53 : ZMod 2)=1 from rfl), (show (54 : ZMod 2)=0 from rfl), (show (55 : ZMod 2)=1 from rfl), (show (56 : ZMod 2)=0 from rfl), (show (57 : ZMod 2)=1 from rfl), (show (58 : ZMod 2)=0 from rfl), (show (59 : ZMod 2)=1 from rfl), (show (60 : ZMod 2)=0 from rfl), (show (61 : ZMod 2)=1 from rfl), (show (62 : ZMod 2)=0 from rfl), (show (63 : ZMod 2)=1 from rfl), (show (64 : ZMod 2)=0 from rfl), mul_zero, mul_one, add_zero, zero_add, sub_zero] <;> ring

end Atlas.Algebra
