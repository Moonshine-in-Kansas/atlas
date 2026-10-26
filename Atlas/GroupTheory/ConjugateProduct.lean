import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Atlas.GroupTheory

/-- The ordered product of successive conjugates, without a commutativity assumption. -/
theorem conjugate_product_formula {G : Type*} [Group G] (p r : G) (n : ℕ) :
    ((List.range n).map (fun j => p^j*r*(p^j)⁻¹)).prod = (r*p)^n*(p^n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ih, pow_succ]
    group

end Atlas.GroupTheory
