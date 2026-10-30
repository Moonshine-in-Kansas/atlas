import Atlas.LinearGroups.Chevalley.Comparison.F4.SparseIntegralMatrix

/-! Sparse integer coefficient-list semantics. These proofs are uniform in
the dimensions and lists; no literal matrix computation is performed here.
Repeated entries, zero coefficients and cancellation are all permitted. -/
namespace Atlas.LinearAlgebra.SparseIntegralMatrix
variable {m n : ℕ}

/-- Multiply every entry coefficient, without sorting or removing zeros. -/
def scaleEntries (a : ℤ) (L : List (Entry n)) : List (Entry n) :=
  L.map (fun e => (e.1, e.2.1, a * e.2.2))

theorem denote_scaleEntries (a : ℤ) (L : List (Entry n)) :
    denote (scaleEntries a L) = a • denote L := by
  induction L with
  | nil => simp [scaleEntries]
  | cons e L ih =>
    simp only [scaleEntries, List.map_cons, denote_cons] at ih ⊢
    rw [ih, smul_add, Matrix.smul_single, Int.zsmul_eq_mul]

/-- A raw sparse expression for subtraction. -/
def subEntries (L M : List (Entry n)) : List (Entry n) :=
  L ++ scaleEntries (-1) M

theorem denote_subEntries (L M : List (Entry n)) :
    denote (subEntries L M) = denote L - denote M := by
  simp only [subEntries, denote_append, denote_scaleEntries,
    neg_one_smul, sub_eq_add_neg]

/-- The entries in column `j` of `L` select and scale the corresponding
lists in `B`. No uniqueness or support hypothesis on either list is needed. -/
def columnEntries (B : Fin m → List (Entry n)) (L : List (Entry m))
    (j : Fin m) : List (Entry n) :=
  L.flatMap (fun e =>
    if e.2.1 = j then scaleEntries e.2.2 (B e.1) else [])

private theorem sum_single_column_smul
    (C : Fin m → Matrix (Fin n) (Fin n) ℤ) (e : Entry m) (j : Fin m) :
    (∑ k : Fin m, Matrix.single e.1 e.2.1 e.2.2 k j • C k) =
      if e.2.1 = j then e.2.2 • C e.1 else 0 := by
  by_cases h : e.2.1 = j <;> simp [Matrix.single_apply, h, ite_smul]

/-- A coefficient column acts on a family of sparse matrices by selecting
and concatenating scaled lists. The proof is list induction, not evaluation. -/
theorem denote_columnEntries (B : Fin m → List (Entry n))
    (L : List (Entry m)) (j : Fin m) :
    denote (columnEntries B L j) =
      ∑ k : Fin m, denote L k j • denote (B k) := by
  induction L with
  | nil => simp [columnEntries]
  | cons e L ih =>
    have hc : columnEntries B (e :: L) j =
        (if e.2.1 = j then scaleEntries e.2.2 (B e.1) else []) ++
          columnEntries B L j := by
      simp only [columnEntries, List.flatMap_cons]
    rw [hc, denote_append, ih]
    simp only [denote_cons, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    rw [sum_single_column_smul (fun k => denote (B k)) e j]
    by_cases h : e.2.1 = j <;>
      simp only [h, ite_true, ite_false, denote_scaleEntries, denote_nil]

end Atlas.LinearAlgebra.SparseIntegralMatrix
