import Atlas.LinearGroups.SuzukiFamily.Twist
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Literal four-coordinate matrices in the lower-triangular column convention. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def norm (m : ℕ) (a b : F) : F := a^2 * theta F m a + a*b + theta F m b

def u (m : ℕ) (a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,0; a,1,0,0; a*theta F m a+b,theta F m a,1,0; norm m a b,b,a,1]

def h (m : ℕ) (t : Fˣ) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![(t:F)*theta F m (t:F),(t:F),↑(t⁻¹),↑(t⁻¹)*theta F m ↑(t⁻¹)]

def w : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,0,1;0,0,1,0;0,1,0,0;1,0,0,0]

theorem u_injective (m : ℕ) : Function.Injective (fun p : F × F => u m p.1 p.2) := by
  intro p q he
  have ha := congrArg (fun A => A 1 0) he
  have hb := congrArg (fun A => A 3 1) he
  exact Prod.ext ha hb

@[simp] theorem u_zero (m : ℕ) : u m (0:F) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u,norm,theta_apply,Matrix.one_apply]

@[simp] theorem w_square : (w : Matrix (Fin 4) (Fin 4) F) * w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [w,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
end Atlas.SuzukiFamily
