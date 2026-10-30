import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-! A proof-producing sparse multiplication interface for small integer
matrices. Lists are raw expressions; no external normalization is trusted.
-/
namespace Atlas.LinearAlgebra.SparseIntegralMatrix
variable {n : ℕ}
abbrev Entry (n : ℕ) := Fin n × Fin n × ℤ

def denote (L : List (Entry n)) : Matrix (Fin n) (Fin n) ℤ :=
  (L.map (fun e => Matrix.single e.1 e.2.1 e.2.2)).sum

@[simp] theorem denote_nil : denote ([] : List (Entry n)) = 0 := rfl
@[simp] theorem denote_cons (e : Entry n) (L : List (Entry n)) :
    denote (e::L) = Matrix.single e.1 e.2.1 e.2.2 + denote L := rfl
@[simp] theorem denote_append (L M : List (Entry n)) :
    denote (L++M) = denote L + denote M := by
  simp [denote, List.map_append, List.sum_append]

def pairProduct (e f : Entry n) : List (Entry n) :=
  if e.2.1=f.1 then [(e.1,f.2.1,e.2.2*f.2.2)] else []

def product (L M : List (Entry n)) : List (Entry n) :=
  L.flatMap (fun e => M.flatMap (pairProduct e))

theorem denote_pairProduct (e f : Entry n) :
    denote (pairProduct e f) =
      Matrix.single e.1 e.2.1 e.2.2 * Matrix.single f.1 f.2.1 f.2.2 := by
  by_cases h : e.2.1=f.1
  · rw [pairProduct, if_pos h]
    simp only [denote_cons, denote_nil, add_zero]
    rw [h, Matrix.single_mul_single_same]
  · simp [pairProduct, h, Matrix.single_mul_single_of_ne e.2.2 e.1 e.2.1 f.1 h f.2.2]

private theorem denote_leftProduct (e : Entry n) (M : List (Entry n)) :
    denote (M.flatMap (pairProduct e)) =
      Matrix.single e.1 e.2.1 e.2.2 * denote M := by
  induction M with
  | nil => simp [denote]
  | cons f M ih =>
    simp only [List.flatMap_cons, denote_append, denote_cons, mul_add,
      denote_pairProduct, ih]

theorem denote_product (L M : List (Entry n)) :
    denote (product L M) = denote L * denote M := by
  induction L with
  | nil => simp [product]
  | cons e L ih =>
    simp only [product, List.flatMap_cons, denote_append, denote_cons,
      add_mul, denote_leftProduct] at ih ⊢
    rw [ih]

end Atlas.LinearAlgebra.SparseIntegralMatrix
