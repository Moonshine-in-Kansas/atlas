import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Geometric coordinates of the Version 33 Conway–Wales construction.
The old quaternionic seed construction is not an input to this module. -/
namespace Atlas.Rudvalis

abbrev Bit := ZMod 2
abbrev E := Fin 3 → Bit
abbrev Point := {p : E // p ≠ 0}
abbrev Coordinate := Point × E

def binaryLabel (i : Fin 8) : E :=
  ![![0,0,0], ![1,0,0], ![0,1,0], ![1,1,0],
    ![0,0,1], ![1,0,1], ![0,1,1], ![1,1,1]] i

theorem binaryLabel_bijective : Function.Bijective binaryLabel := by decide

noncomputable def innerEquiv : Fin 8 ≃ E := Equiv.ofBijective binaryLabel binaryLabel_bijective

def rowLabel (i : Fin 7) : Point :=
  ⟨binaryLabel (![6,1,5,7,4,2,3] i), by fin_cases i <;> decide⟩

theorem rowLabel_bijective : Function.Bijective rowLabel := by decide

noncomputable def rowEquiv : Fin 7 ≃ Point := Equiv.ofBijective rowLabel rowLabel_bijective

@[simp] theorem card_E : Fintype.card E = 8 := by decide
@[simp] theorem card_Point : Fintype.card Point = 7 := by decide
@[simp] theorem card_Coordinate : Fintype.card Coordinate = 56 := by decide

open scoped BigOperators

def dot (x y : E) : Bit := ∑ i, x i * y i

theorem dot_add_left (x y z : E) : dot (x+y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right (x y z : E) : dot x (y+z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul_left (a : Bit) (x y : E) : dot (a • x) y = a * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_comm (x y : E) : dot x y = dot y x := by simp [dot, mul_comm]

/-- The common quadratic class, with least significant coordinate first. -/
def quadratic (c x : E) : Bit :=
  c 0 * x 1 * x 2 + c 1 * x 0 * x 2 + c 2 * x 0 * x 1

/-- The literal three columns of Table eta, indexed by the geometric point. -/
def etaColumn (p : Point) (i : Fin 3) : E :=
  binaryLabel ((if p.val = binaryLabel 1 then ![3,4,3]
    else if p.val = binaryLabel 2 then ![6,2,3]
    else if p.val = binaryLabel 3 then ![4,5,3]
    else if p.val = binaryLabel 4 then ![0,0,7]
    else if p.val = binaryLabel 5 then ![6,5,2]
    else if p.val = binaryLabel 6 then ![2,5,0]
    else ![6,1,1]) i)

def eta (p : Point) (c : E) : E := ∑ i, c i • etaColumn p i

def theta (p : Point) (c x : E) : Bit := quadratic c x + dot (eta p c) x

theorem theta_zero (p : Point) (c : E) : theta p c 0 = 0 := by
  simp [theta, quadratic, dot]

theorem theta_normalization (p : Point) (c : E) :
    theta p c c = if p.val = c then 1 else 0 := by decide +kernel +revert

theorem eta_add (p : Point) (c d : E) : eta p (c+d) = eta p c + eta p d := by
  simp [eta, add_smul, Finset.sum_add_distrib]

theorem quadratic_add_parameter (c d x : E) :
    quadratic (c+d) x = quadratic c x + quadratic d x := by
  simp [quadratic]; ring

theorem theta_add_parameter (p : Point) (c d x : E) :
    theta p (c+d) x = theta p c x + theta p d x := by
  rw [theta, eta_add, quadratic_add_parameter, dot_add_left]
  simp only [theta]; ring

/-- The determinant polar form in characteristic two. -/
def polar (c x y : E) : Bit :=
  c 0 * (x 1*y 2+x 2*y 1) + c 1 * (x 0*y 2+x 2*y 0) +
    c 2 * (x 0*y 1+x 1*y 0)

theorem theta_polarization (p : Point) (c x y : E) :
    theta p c (x+y) + theta p c x + theta p c y = polar c x y := by
  simp [theta, quadratic, dot, polar, Fin.sum_univ_succ]
  ring_nf
  have htwo : (2 : Bit) = 0 := by decide
  simp [htwo]

end Atlas.Rudvalis

