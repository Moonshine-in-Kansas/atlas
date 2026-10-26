import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-! Concrete rank-six integral lattice for the exceptional order-25920 bridge.
The diagram has edges 01,12,23,34,25. No finite-group identification is assumed. -/
namespace Atlas.Comparisons.E6Lattice

def gram : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
     0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2]

def norm {R : Type*} [CommRing R] (x : Fin 6 → R) : R :=
  x 0^2 + x 1^2 + x 2^2 + x 3^2 + x 4^2 + x 5^2 -
    x 0*x 1 - x 1*x 2 - x 2*x 3 - x 3*x 4 - x 2*x 5

/-- The same integral polynomial as a quadratic form over any coefficient ring. -/
def form (R : Type*) [CommRing R] : QuadraticForm R (Fin 6 → R) :=
  QuadraticMap.proj 0 0 + QuadraticMap.proj 1 1 + QuadraticMap.proj 2 2 +
    QuadraticMap.proj 3 3 + QuadraticMap.proj 4 4 + QuadraticMap.proj 5 5 -
    QuadraticMap.proj 0 1 - QuadraticMap.proj 1 2 - QuadraticMap.proj 2 3 -
    QuadraticMap.proj 3 4 - QuadraticMap.proj 2 5

@[simp] theorem form_apply {R : Type*} [CommRing R] (x : Fin 6 → R) :
    form R x = norm x := by simp [form,norm,pow_two]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Explicit six-by-six determinant reduction uses a larger reduction budget.
theorem gram_det : gram.det = 3 := by
  norm_num [gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero]
  decide

theorem norm_square_decomposition (x : Fin 6 → ℤ) :
    120 * norm x =
      30*(2*x 0-x 1)^2 + 10*(3*x 1-2*x 2)^2 +
      5*(4*x 2-3*x 3-3*x 5)^2 + 3*(5*x 3-4*x 4-3*x 5)^2 +
      18*(2*x 4-x 5)^2 + 30*x 5^2 := by
  unfold norm
  ring

theorem norm_nonneg (x : Fin 6 → ℤ) : 0 ≤ norm x := by
  have h := norm_square_decomposition x
  nlinarith [sq_nonneg (2*x 0-x 1),sq_nonneg (3*x 1-2*x 2),
    sq_nonneg (4*x 2-3*x 3-3*x 5),sq_nonneg (5*x 3-4*x 4-3*x 5),
    sq_nonneg (2*x 4-x 5),sq_nonneg (x 5)]

theorem norm_eq_zero_iff (x : Fin 6 → ℤ) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h := norm_square_decomposition x
    rw [hx] at h
    have h0 := sq_nonneg (2*x 0-x 1)
    have h1 := sq_nonneg (3*x 1-2*x 2)
    have h2 := sq_nonneg (4*x 2-3*x 3-3*x 5)
    have h3 := sq_nonneg (5*x 3-4*x 4-3*x 5)
    have h4 := sq_nonneg (2*x 4-x 5)
    have h5 := sq_nonneg (x 5)
    have e5 : x 5 = 0 := by nlinarith
    have e4 : x 4 = 0 := by rw [e5] at h4 h; nlinarith
    have e3 : x 3 = 0 := by rw [e5,e4] at h3 h; nlinarith
    have e2 : x 2 = 0 := by rw [e5,e3] at h2 h; nlinarith
    have e1 : x 1 = 0 := by rw [e2] at h1 h; nlinarith
    have e0 : x 0 = 0 := by rw [e1] at h0 h; nlinarith
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    simp [norm]

/-- Integral simple reflection; the changed coordinate is the sum of its neighbors
minus itself. This formula reduces in every characteristic. -/
def reflection {R : Type*} [CommRing R] (i : Fin 6) (x : Fin 6 → R) : Fin 6 → R :=
  Function.update x i (match i with
    | 0 => x 1-x 0
    | 1 => x 0+x 2-x 1
    | 2 => x 1+x 3+x 5-x 2
    | 3 => x 2+x 4-x 3
    | 4 => x 3-x 4
    | 5 => x 2-x 5)

theorem reflection_norm {R : Type*} [CommRing R] (i : Fin 6) (x : Fin 6 → R) :
    norm (reflection i x) = norm x := by
  fin_cases i <;> simp [reflection,norm] <;> ring

theorem reflection_involutive {R : Type*} [CommRing R] (i : Fin 6) :
    Function.Involutive (reflection (R := R) i) := by
  intro x
  funext j
  fin_cases i <;> fin_cases j <;> simp [reflection]

/-- Exact nonsingular-vector count for the full binary six-coordinate space. -/
theorem binary_nonsingular_count :
    Fintype.card {x : Fin 6 → ZMod 2 // norm x = 1} = 36 := by decide

end Atlas.Comparisons.E6Lattice

