import Mathlib.Algebra.Quaternion
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Exact Conway–Wales seed coordinates, v15 Table `tab:seeds`.
The complex unit is central; the quaternion basis is (1,j,k,l). -/
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Atlas.ConwayWales

abbrev Row := Fin 7
abbrev Q := Quaternion ℂ
abbrev Space := Row → Q

def j : Q := ⟨0, 1, 0, 0⟩
def k : Q := ⟨0, 0, 1, 0⟩
def l : Q := ⟨0, 0, 0, 1⟩
def centralI : Q := ⟨Complex.I, 0, 0, 0⟩

def dagger (x : Q) : Q := ⟨star x.re, -star x.imI, -star x.imJ, -star x.imK⟩

def A : Space := ![⟨1,1,1,1⟩, 0, 0, ⟨Complex.I,1,Complex.I,-1⟩,
  0, ⟨Complex.I,Complex.I,-1,1⟩, ⟨Complex.I,-1,1,Complex.I⟩]
def B : Space := ![⟨Complex.I,1,1,1⟩, ⟨Complex.I,0,0,-1⟩,
  ⟨Complex.I,-1,0,0⟩, ⟨0,0,-1,1⟩, ⟨Complex.I,0,-1,0⟩,
  ⟨0,-1,1,0⟩, ⟨0,1,0,-1⟩]

def a : Space := fun r => (1 / 2 : ℂ) • A r
def b : Space := fun r => (1 / 2 : ℂ) • B r

def hermitian (v w : Space) : ℂ := ∑ r, (dagger (v r) * w r).re

def coefficient (r : Row) : Q := -centralI * B r

theorem j_sq : j * j = -1 := by ext <;> norm_num [j]
theorem k_sq : k * k = -1 := by ext <;> norm_num [k]
theorem l_sq : l * l = -1 := by ext <;> norm_num [l]
theorem j_mul_k : j * k = l := by ext <;> norm_num [j,k,l]
theorem k_mul_j : k * j = -l := by ext <;> norm_num [j,k,l]
theorem centralI_sq : centralI * centralI = -1 := by
  ext <;> norm_num [centralI]

theorem centralI_commutes (x : Q) : centralI * x = x * centralI := by
  ext <;> simp [centralI, mul_comm]

theorem dagger_dagger (x : Q) : dagger (dagger x) = x := by
  ext <;> simp [dagger]

theorem norm_a : hermitian a a = 4 := by
  norm_num [hermitian, a, A, dagger, Fin.sum_univ_succ]
  ring_nf
  norm_num

theorem norm_b : hermitian b b = 4 := by
  norm_num [hermitian, b, B, dagger, Fin.sum_univ_succ]
  ring_nf
  norm_num

theorem coefficient_self_adjoint (r : Row) : dagger (coefficient r) = coefficient r := by
  fin_cases r <;> ext <;> norm_num [coefficient, centralI, B, dagger]


theorem correlation_zero : (∑ r : Row, coefficient r * coefficient r) = 16 := by
  simp only [Fin.sum_univ_succ]
  dsimp [coefficient, centralI, B]
  ext <;> norm_num <;> ring_nf <;> rfl

theorem correlation_one : (∑ r : Row, coefficient r * coefficient (r + 1)) = 0 := by
  simp only [Fin.sum_univ_succ]
  dsimp [coefficient, centralI, B]
  ext <;> norm_num <;> ring_nf <;> rfl


set_option maxHeartbeats 1600000 in
theorem correlation (d : Row) :
    (∑ r : Row, coefficient r * coefficient (r + d)) = if d = 0 then 16 else 0 := by
  fin_cases d <;> simp only [Fin.sum_univ_succ]
  all_goals dsimp [coefficient, centralI, B]
  all_goals ext <;> norm_num <;> ring_nf <;> rfl

def convolution (v : Space) : Space := fun r =>
  (1 / 4 : ℂ) • ∑ s : Row, coefficient (r + s) * v s

def f : Space := fun r => if r = 0 then ⟨2 * Complex.I, 0, 0, 0⟩ else 0

def C : Space := ![⟨1,-Complex.I,-Complex.I,-Complex.I⟩,
  ⟨0,1,Complex.I,0⟩, ⟨0,0,1,Complex.I⟩, ⟨Complex.I,Complex.I,0,0⟩,
  ⟨0,Complex.I,0,1⟩, ⟨Complex.I,0,0,Complex.I⟩, ⟨Complex.I,0,Complex.I,0⟩]
def c : Space := fun r => (1 / 2 : ℂ) • C r

set_option maxHeartbeats 1600000 in
theorem convolution_f : convolution f = b := by
  funext r
  fin_cases r <;> simp only [convolution, Fin.sum_univ_succ]
  all_goals dsimp [coefficient, centralI, B, f, b]
  all_goals ext <;> norm_num <;> ring_nf <;> norm_num

set_option maxHeartbeats 1600000 in
theorem convolution_b : convolution b = f := by
  funext r
  fin_cases r <;> simp only [convolution, Fin.sum_univ_succ]
  all_goals dsimp [coefficient, centralI, B, f, b]
  all_goals ext <;> norm_num <;> ring_nf <;> norm_num

set_option maxHeartbeats 1600000 in
theorem convolution_a : convolution a = c := by
  funext r
  fin_cases r <;> simp only [convolution, Fin.sum_univ_succ]
  all_goals dsimp [coefficient, centralI, B, A, C, a, c]
  all_goals ext <;> norm_num <;> ring_nf <;> norm_num

end Atlas.ConwayWales
