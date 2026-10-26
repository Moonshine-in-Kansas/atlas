import Mathlib.Data.Matrix.Basic

/-! Connectivity proved from a decreasing tree of nonzero matrix entries.
No group, root system, or target cardinality occurs. -/
namespace Atlas.LinearAlgebra

def MatrixAdjacencyConnected {ι R : Type*} [Zero R] (C : Matrix ι ι R) : Prop :=
  ∀ S : Set ι, (∀ i ∈ S, ∀ j, C i j ≠ 0 → j ∈ S) → S = ∅ ∨ S = Set.univ

theorem matrixAdjacencyConnected_of_descent {ι R : Type*} [Zero R]
    (C : Matrix ι ι R) (root : ι) (distance : ι → ℕ)
    (hparent : ∀ i, i ≠ root → ∃ j, distance j < distance i ∧
      C i j ≠ 0 ∧ C j i ≠ 0) : MatrixAdjacencyConnected C := by
  intro S hS
  have hc : ∀ n i, distance i = n → (i ∈ S ↔ root ∈ S) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      by_cases he : i = root
      · simp only [he]
      · obtain ⟨j, hj, hij, hji⟩ := hparent i he
        have ht := ih (distance j) (by simpa only [hi] using hj) j rfl
        exact (Iff.intro (fun hx => hS i hx j hij)
          (fun hx => hS j hx i hji)).trans ht
  by_cases hr : root ∈ S
  · right
    apply Set.eq_univ_of_forall
    intro i
    exact (hc (distance i) i rfl).mpr hr
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hr ((hc (distance i) i rfl).mp hi)

theorem matrixAdjacencyConnected_reindex {ι κ R : Type*} [Zero R]
    (C : Matrix ι ι R) (D : Matrix κ κ R) (e : ι ≃ κ)
    (he : ∀ i j, D (e i) (e j) = C i j)
    (hC : MatrixAdjacencyConnected C) : MatrixAdjacencyConnected D := by
  intro S hS
  have hc : ∀ i ∈ e ⁻¹' S, ∀ j, C i j ≠ 0 → j ∈ e ⁻¹' S := by
    intro i hi j hij
    exact hS (e i) hi (e j) (by rwa [he])
  rcases hC (e ⁻¹' S) hc with h | h
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have : e.symm j ∈ e ⁻¹' S := by simpa using hj
    simpa [h] using this
  · right
    apply Set.eq_univ_of_forall
    intro j
    have : e.symm j ∈ e ⁻¹' S := by rw [h]; trivial
    simpa using this

end Atlas.LinearAlgebra
