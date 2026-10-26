import Mathlib.Tactic

/-! Four-coordinate minuscule template. Coordinates are e1,e2,-e1,-e2.
Its identification with the actual selected-weight block is a separate obligation. -/
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open scoped Matrix
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def ea : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,1,0,0; 0,0,0,0; 0,0,0,0; 0,0,1,0]
def fa : Matrix (Fin 4) (Fin 4) ℤ := ea.transpose
def eb : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,0,0,0; 0,0,0,1; 0,0,0,0; 0,0,0,0]
def fb : Matrix (Fin 4) (Fin 4) ℤ := eb.transpose

def na : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,1,0,0; -1,0,0,0; 0,0,0,-1; 0,0,1,0]
def naInv : Matrix (Fin 4) (Fin 4) ℤ := -na
def nb : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,-1,0,0]
def nbInv : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,0,0,0; 0,0,0,-1; 0,0,1,0; 0,1,0,0]

def za : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,0,0,-1; 0,0,1,0; 0,0,0,0; 0,0,0,0]
def wb : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,0,-1,0; 0,0,0,0; 0,0,0,0; 0,0,0,0]

theorem na_word : (1 + ea) * (1 - fa) * (1 + ea) = na := by decide
theorem nb_word : (1 + eb) * (1 - fb) * (1 + eb) = nb := by decide
theorem na_inverse : na * naInv = 1 := by decide
theorem na_inverse_left : naInv * na = 1 := by decide
theorem nb_inverse : nb * nbInv = 1 := by decide
theorem nb_inverse_left : nbInv * nb = 1 := by decide
theorem nb_ea_conjugate : nb * ea * nbInv = za := by decide
theorem na_eb_conjugate : na * eb * naInv = wb := by decide

variable {R : Type*} [CommRing R]

def XA (s : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + s • ea.map (Int.castRingHom R)
def XB (s : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + s • eb.map (Int.castRingHom R)
def YA (s : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + s • fa.map (Int.castRingHom R)
def YB (s : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + s • fb.map (Int.castRingHom R)
def Z (s : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + s • za.map (Int.castRingHom R)
def W (s : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + s • wb.map (Int.castRingHom R)

/-- These signs agree with the actual ten-dimensional adjoint pinning. -/
theorem same_root_relation (s t : R) :
    XA s * Z t = W (-2*s*t) * Z t * XA s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, Z, W, ea, za, wb, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

theorem mixed_root_relation (s t : R) :
    XA s * XB t = Z (-s*t) * W (s^2*t) * XB t * XA s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [XA, XB, Z, W, ea, eb, za, wb, Matrix.vecCons,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
    norm_num [Matrix.one_apply, Fin.ext_iff] <;> ring

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule
