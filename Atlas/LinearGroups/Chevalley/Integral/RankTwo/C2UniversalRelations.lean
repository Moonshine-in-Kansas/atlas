import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2IntegerTemplate
import Mathlib.Tactic

/-! Universal commutative-ring C2 matrix identities. Each finite row is checked
using ring normalization. Actual Geck correspondence is supplied separately
before these identities are used as relations in the generated group. -/
namespace Atlas.Chevalley.Integral.RankTwo.C2UniversalRelations
open scoped Matrix
open C2IntegerTemplate
variable {R : Type*} [CommRing R]

def XA (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • ea.map (Int.castRingHom R) + t^2 • ea2.map (Int.castRingHom R)
def XB (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • eb.map (Int.castRingHom R) + t^2 • eb2.map (Int.castRingHom R)
def Z (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • za.map (Int.castRingHom R) + t^2 • za2.map (Int.castRingHom R)
def W (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • wb.map (Int.castRingHom R) + t^2 • wb2.map (Int.castRingHom R)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def sameLeft (s t : R) : Matrix (Fin 10) (Fin 10) R :=
  !![(1 : R), 0, 0, 0, 0, 0, s, 0, (-1 : R) * t, s * t;
    0, (1 : R), 0, 0, 0, 0, 0, 0, (2 : R) * t, 0;
    (2 : R) * s, s, (1 : R), 0, 0, 0, s^2, (-1 : R) * t, 0, s^2 * t;
    0, 0, 0, (1 : R), 0, 0, (2 : R) * t, 0, 0, t^2;
    0, (-1 : R) * t, 0, s, (1 : R), 0, (2 : R) * s * t, 0, (-1 : R) * t^2, s * t^2;
    0, (-2 : R) * s * t, (-2 : R) * t, s^2, (2 : R) * s, (1 : R), (2 : R) * s^2 * t, t^2, (-2 : R) * s * t^2, s^2 * t^2;
    0, 0, 0, 0, 0, 0, (1 : R), 0, 0, t;
    0, 0, 0, 0, 0, 0, 0, (1 : R), (2 : R) * s, s^2;
    0, 0, 0, 0, 0, 0, 0, 0, (1 : R), s;
    0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : R)]

def samePrefix (s t : R) : Matrix (Fin 10) (Fin 10) R :=
  !![(1 : R), 0, 0, 0, 0, 0, 0, 0, (-1 : R) * t, (2 : R) * s * t;
    0, (1 : R), 0, 0, 0, 0, 0, 0, (2 : R) * t, (-2 : R) * s * t;
    0, 0, (1 : R), 0, 0, 0, 0, (-1 : R) * t, (2 : R) * s * t, 0;
    0, 0, 0, (1 : R), 0, 0, (2 : R) * t, 0, 0, t^2;
    0, (-1 : R) * t, 0, 0, (1 : R), 0, (2 : R) * s * t, 0, (-1 : R) * t^2, (2 : R) * s * t^2;
    (4 : R) * s * t, 0, (-2 : R) * t, 0, 0, (1 : R), 0, t^2, (-4 : R) * s * t^2, (4 : R) * s^2 * t^2;
    0, 0, 0, 0, 0, 0, (1 : R), 0, 0, t;
    0, 0, 0, 0, 0, 0, 0, (1 : R), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (1 : R), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : R)]

def mixedLeft (s t : R) : Matrix (Fin 10) (Fin 10) R :=
  !![(1 : R), 0, 0, 0, 0, 0, s, 0, s * t, 0;
    0, (1 : R), 0, 0, 0, 0, 0, t, 0, 0;
    (2 : R) * s, s, (1 : R), 0, 0, 0, s^2, s * t, s^2 * t, 0;
    (2 : R) * t, (2 : R) * t, 0, (1 : R), 0, 0, 0, t^2, 0, 0;
    (2 : R) * s * t, (2 : R) * s * t, t, s, (1 : R), 0, 0, s * t^2, 0, 0;
    (2 : R) * s^2 * t, (2 : R) * s^2 * t, (2 : R) * s * t, s^2, (2 : R) * s, (1 : R), 0, s^2 * t^2, 0, 0;
    0, 0, 0, 0, 0, 0, (1 : R), 0, t, 0;
    0, 0, 0, 0, 0, 0, 0, (1 : R), (2 : R) * s, s^2;
    0, 0, 0, 0, 0, 0, 0, 0, (1 : R), s;
    0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : R)]

def mixedPrefix (s t : R) : Matrix (Fin 10) (Fin 10) R :=
  !![(1 : R), 0, 0, 0, 0, 0, 0, 0, s * t, (-1 : R) * s^2 * t;
    0, (1 : R), 0, 0, 0, 0, 0, 0, (-2 : R) * s * t, s^2 * t;
    0, 0, (1 : R), 0, 0, 0, 0, s * t, (-1 : R) * s^2 * t, 0;
    0, 0, 0, (1 : R), 0, 0, (-2 : R) * s * t, 0, 0, s^2 * t^2;
    0, s * t, 0, 0, (1 : R), 0, (-1 : R) * s^2 * t, 0, (-1 : R) * s^2 * t^2, s^3 * t^2;
    (-2 : R) * s^2 * t, 0, (2 : R) * s * t, 0, 0, (1 : R), 0, s^2 * t^2, (-2 : R) * s^3 * t^2, s^4 * t^2;
    0, 0, 0, 0, 0, 0, (1 : R), 0, 0, (-1 : R) * s * t;
    0, 0, 0, 0, 0, 0, 0, (1 : R), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (1 : R), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : R)]

def mixedPrefixB (s t : R) : Matrix (Fin 10) (Fin 10) R :=
  !![(1 : R), 0, 0, 0, 0, 0, 0, 0, s * t, (-1 : R) * s^2 * t;
    0, (1 : R), 0, 0, 0, 0, 0, t, (-2 : R) * s * t, s^2 * t;
    0, 0, (1 : R), 0, 0, 0, 0, s * t, (-1 : R) * s^2 * t, 0;
    (2 : R) * t, (2 : R) * t, 0, (1 : R), 0, 0, (-2 : R) * s * t, t^2, (-2 : R) * s * t^2, s^2 * t^2;
    0, s * t, t, 0, (1 : R), 0, (-1 : R) * s^2 * t, s * t^2, (-2 : R) * s^2 * t^2, s^3 * t^2;
    (-2 : R) * s^2 * t, 0, (2 : R) * s * t, 0, 0, (1 : R), 0, s^2 * t^2, (-2 : R) * s^3 * t^2, s^4 * t^2;
    0, 0, 0, 0, 0, 0, (1 : R), 0, t, (-1 : R) * s * t;
    0, 0, 0, 0, 0, 0, 0, (1 : R), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (1 : R), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : R)]

private theorem same_left_product_row0 (s t : R) (j : Fin 10) :
    (XA s * Z t) 0 j = (sameLeft s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row1 (s t : R) (j : Fin 10) :
    (XA s * Z t) 1 j = (sameLeft s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row2 (s t : R) (j : Fin 10) :
    (XA s * Z t) 2 j = (sameLeft s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row3 (s t : R) (j : Fin 10) :
    (XA s * Z t) 3 j = (sameLeft s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row4 (s t : R) (j : Fin 10) :
    (XA s * Z t) 4 j = (sameLeft s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row5 (s t : R) (j : Fin 10) :
    (XA s * Z t) 5 j = (sameLeft s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row6 (s t : R) (j : Fin 10) :
    (XA s * Z t) 6 j = (sameLeft s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row7 (s t : R) (j : Fin 10) :
    (XA s * Z t) 7 j = (sameLeft s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row8 (s t : R) (j : Fin 10) :
    (XA s * Z t) 8 j = (sameLeft s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_left_product_row9 (s t : R) (j : Fin 10) :
    (XA s * Z t) 9 j = (sameLeft s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem same_left_product (s t : R) : XA s * Z t = (sameLeft s t) := by
  ext i j
  fin_cases i
  · exact same_left_product_row0 s t j
  · exact same_left_product_row1 s t j
  · exact same_left_product_row2 s t j
  · exact same_left_product_row3 s t j
  · exact same_left_product_row4 s t j
  · exact same_left_product_row5 s t j
  · exact same_left_product_row6 s t j
  · exact same_left_product_row7 s t j
  · exact same_left_product_row8 s t j
  · exact same_left_product_row9 s t j

private theorem same_prefix_product_row0 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 0 j = (samePrefix s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row1 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 1 j = (samePrefix s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row2 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 2 j = (samePrefix s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row3 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 3 j = (samePrefix s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row4 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 4 j = (samePrefix s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row5 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 5 j = (samePrefix s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row6 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 6 j = (samePrefix s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row7 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 7 j = (samePrefix s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row8 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 8 j = (samePrefix s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_prefix_product_row9 (s t : R) (j : Fin 10) :
    (W (-2*s*t) * Z t) 9 j = (samePrefix s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem same_prefix_product (s t : R) : W (-2*s*t) * Z t = (samePrefix s t) := by
  ext i j
  fin_cases i
  · exact same_prefix_product_row0 s t j
  · exact same_prefix_product_row1 s t j
  · exact same_prefix_product_row2 s t j
  · exact same_prefix_product_row3 s t j
  · exact same_prefix_product_row4 s t j
  · exact same_prefix_product_row5 s t j
  · exact same_prefix_product_row6 s t j
  · exact same_prefix_product_row7 s t j
  · exact same_prefix_product_row8 s t j
  · exact same_prefix_product_row9 s t j

private theorem same_final_product_row0 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 0 j = (sameLeft s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row1 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 1 j = (sameLeft s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row2 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 2 j = (sameLeft s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row3 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 3 j = (sameLeft s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row4 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 4 j = (sameLeft s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row5 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 5 j = (sameLeft s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row6 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 6 j = (sameLeft s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row7 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 7 j = (sameLeft s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row8 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 8 j = (sameLeft s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem same_final_product_row9 (s t : R) (j : Fin 10) :
    ((samePrefix s t) * XA s) 9 j = (sameLeft s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem same_final_product (s t : R) : (samePrefix s t) * XA s = (sameLeft s t) := by
  ext i j
  fin_cases i
  · exact same_final_product_row0 s t j
  · exact same_final_product_row1 s t j
  · exact same_final_product_row2 s t j
  · exact same_final_product_row3 s t j
  · exact same_final_product_row4 s t j
  · exact same_final_product_row5 s t j
  · exact same_final_product_row6 s t j
  · exact same_final_product_row7 s t j
  · exact same_final_product_row8 s t j
  · exact same_final_product_row9 s t j

private theorem mixed_left_product_row0 (s t : R) (j : Fin 10) :
    (XA s * XB t) 0 j = (mixedLeft s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row1 (s t : R) (j : Fin 10) :
    (XA s * XB t) 1 j = (mixedLeft s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row2 (s t : R) (j : Fin 10) :
    (XA s * XB t) 2 j = (mixedLeft s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row3 (s t : R) (j : Fin 10) :
    (XA s * XB t) 3 j = (mixedLeft s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row4 (s t : R) (j : Fin 10) :
    (XA s * XB t) 4 j = (mixedLeft s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row5 (s t : R) (j : Fin 10) :
    (XA s * XB t) 5 j = (mixedLeft s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row6 (s t : R) (j : Fin 10) :
    (XA s * XB t) 6 j = (mixedLeft s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row7 (s t : R) (j : Fin 10) :
    (XA s * XB t) 7 j = (mixedLeft s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row8 (s t : R) (j : Fin 10) :
    (XA s * XB t) 8 j = (mixedLeft s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_left_product_row9 (s t : R) (j : Fin 10) :
    (XA s * XB t) 9 j = (mixedLeft s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem mixed_left_product (s t : R) : XA s * XB t = (mixedLeft s t) := by
  ext i j
  fin_cases i
  · exact mixed_left_product_row0 s t j
  · exact mixed_left_product_row1 s t j
  · exact mixed_left_product_row2 s t j
  · exact mixed_left_product_row3 s t j
  · exact mixed_left_product_row4 s t j
  · exact mixed_left_product_row5 s t j
  · exact mixed_left_product_row6 s t j
  · exact mixed_left_product_row7 s t j
  · exact mixed_left_product_row8 s t j
  · exact mixed_left_product_row9 s t j

private theorem mixed_prefix_product_row0 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 0 j = (mixedPrefix s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row1 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 1 j = (mixedPrefix s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row2 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 2 j = (mixedPrefix s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row3 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 3 j = (mixedPrefix s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row4 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 4 j = (mixedPrefix s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row5 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 5 j = (mixedPrefix s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row6 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 6 j = (mixedPrefix s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row7 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 7 j = (mixedPrefix s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row8 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 8 j = (mixedPrefix s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefix_product_row9 (s t : R) (j : Fin 10) :
    (Z (-s*t) * W (s^2*t)) 9 j = (mixedPrefix s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem mixed_prefix_product (s t : R) : Z (-s*t) * W (s^2*t) = (mixedPrefix s t) := by
  ext i j
  fin_cases i
  · exact mixed_prefix_product_row0 s t j
  · exact mixed_prefix_product_row1 s t j
  · exact mixed_prefix_product_row2 s t j
  · exact mixed_prefix_product_row3 s t j
  · exact mixed_prefix_product_row4 s t j
  · exact mixed_prefix_product_row5 s t j
  · exact mixed_prefix_product_row6 s t j
  · exact mixed_prefix_product_row7 s t j
  · exact mixed_prefix_product_row8 s t j
  · exact mixed_prefix_product_row9 s t j

private theorem mixed_prefixB_product_row0 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 0 j = (mixedPrefixB s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row1 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 1 j = (mixedPrefixB s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row2 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 2 j = (mixedPrefixB s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row3 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 3 j = (mixedPrefixB s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row4 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 4 j = (mixedPrefixB s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row5 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 5 j = (mixedPrefixB s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row6 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 6 j = (mixedPrefixB s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row7 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 7 j = (mixedPrefixB s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row8 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 8 j = (mixedPrefixB s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_prefixB_product_row9 (s t : R) (j : Fin 10) :
    ((mixedPrefix s t) * XB t) 9 j = (mixedPrefixB s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem mixed_prefixB_product (s t : R) : (mixedPrefix s t) * XB t = (mixedPrefixB s t) := by
  ext i j
  fin_cases i
  · exact mixed_prefixB_product_row0 s t j
  · exact mixed_prefixB_product_row1 s t j
  · exact mixed_prefixB_product_row2 s t j
  · exact mixed_prefixB_product_row3 s t j
  · exact mixed_prefixB_product_row4 s t j
  · exact mixed_prefixB_product_row5 s t j
  · exact mixed_prefixB_product_row6 s t j
  · exact mixed_prefixB_product_row7 s t j
  · exact mixed_prefixB_product_row8 s t j
  · exact mixed_prefixB_product_row9 s t j

private theorem mixed_final_product_row0 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 0 j = (mixedLeft s t) 0 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row1 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 1 j = (mixedLeft s t) 1 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row2 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 2 j = (mixedLeft s t) 2 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row3 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 3 j = (mixedLeft s t) 3 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row4 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 4 j = (mixedLeft s t) 4 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row5 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 5 j = (mixedLeft s t) 5 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row6 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 6 j = (mixedLeft s t) 6 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row7 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 7 j = (mixedLeft s t) 7 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row8 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 8 j = (mixedLeft s t) 8 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

private theorem mixed_final_product_row9 (s t : R) (j : Fin 10) :
    ((mixedPrefixB s t) * XA s) 9 j = (mixedLeft s t) 9 j := by
  fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, sameLeft, samePrefix, mixedLeft, mixedPrefix, mixedPrefixB,
      ea, ea2, eb, eb2, za, za2, wb, wb2, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem mixed_final_product (s t : R) : (mixedPrefixB s t) * XA s = (mixedLeft s t) := by
  ext i j
  fin_cases i
  · exact mixed_final_product_row0 s t j
  · exact mixed_final_product_row1 s t j
  · exact mixed_final_product_row2 s t j
  · exact mixed_final_product_row3 s t j
  · exact mixed_final_product_row4 s t j
  · exact mixed_final_product_row5 s t j
  · exact mixed_final_product_row6 s t j
  · exact mixed_final_product_row7 s t j
  · exact mixed_final_product_row8 s t j
  · exact mixed_final_product_row9 s t j

/-- [u,v]=uvu⁻¹v⁻¹ convention: coefficient is minus2. -/
theorem same_root_relation (s t : R) : XA s * Z t =
    W (-2*s*t) * Z t * XA s := by
  rw [same_left_product, same_prefix_product, same_final_product]

/-- The mixed commutator factors are Z(-st), then W(s²t), in that order. -/
theorem mixed_root_relation (s t : R) : XA s * XB t =
    Z (-s*t) * W (s^2*t) * XB t * XA s := by
  rw [mixed_left_product, mixed_prefix_product, mixed_prefixB_product, mixed_final_product]

end Atlas.Chevalley.Integral.RankTwo.C2UniversalRelations
