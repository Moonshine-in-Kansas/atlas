import Atlas.LinearAlgebra.HeightDepth
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Finite products of matrices with a common positive depth bound. Their
first possible homogeneous entries are sums of those of the individual factors. -/

namespace Atlas.Matrix.HeightAtLeast
variable {ι R α : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A finite product of matrices congruent to one at depth d retains that
congruence. The ordering of the factors is preserved. -/
theorem list_prod_sub_one {w : ι → ℤ} {d : ℤ} (hd : 0 ≤ d)
    (f : α → Matrix ι ι R) (l : List α)
    (h : ∀ a ∈ l, HeightAtLeast w d (f a - 1)) :
    HeightAtLeast w d ((l.map f).prod - 1) := by
  induction l with
  | nil =>
    intro row col hlt
    simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl : ∀ x ∈ l, HeightAtLeast w d (f x - 1) := by
      intro x hx
      exact h x (by simp [hx])
    simpa only [List.map_cons, List.prod_cons] using
      HeightAtLeast.mul_sub_one hd ha (ih hl)

/-- At the first positive depth, all cross terms disappear. This statement
keeps an arbitrary finite list and does not assume any commutation relation. -/
theorem list_prod_sub_one_first_degree {w : ι → ℤ} {d : ℤ} (hd : 0 < d)
    (f : α → Matrix ι ι R) (l : List α)
    (h : ∀ a ∈ l, HeightAtLeast w d (f a - 1))
    (row col : ι) (hdegree : w row = w col + d) :
    ((l.map f).prod - 1) row col =
      (l.map (fun a => (f a - 1) row col)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl : ∀ x ∈ l, HeightAtLeast w d (f x - 1) := by
      intro x hx
      exact h x (by simp [hx])
    rw [List.map_cons, List.prod_cons]
    rw [HeightAtLeast.mul_sub_one_first_degree hd ha
      (list_prod_sub_one (le_of_lt hd) f l hl) row col hdegree]
    rw [ih hl]
    rfl

end Atlas.Matrix.HeightAtLeast
