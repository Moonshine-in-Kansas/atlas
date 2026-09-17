import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators

/-- Expand a moment by its four possible levels, without enumerating the domain. -/
theorem four_level_sum {V : Type*} (S : Finset V) (f g : V → ℕ)
    (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (v : ℕ → ℕ) (hf : ∀ x ∈ S, f x = a ∨ f x = b ∨ f x = c ∨ f x = d)
    (hg : ∀ x ∈ S, g x = v (f x)) :
    (∑ x ∈ S, g x) =
      v a * (S.filter (fun x => f x = a)).card +
      v b * (S.filter (fun x => f x = b)).card +
      v c * (S.filter (fun x => f x = c)).card +
      v d * (S.filter (fun x => f x = d)).card := by
  classical
  have he (x : V) (hx : x ∈ S) : g x =
      (if f x = a then v a else 0) + (if f x = b then v b else 0) +
      (if f x = c then v c else 0) + (if f x = d then v d else 0) := by
    rw [hg x hx]
    rcases hf x hx with h | h | h | h <;>
      simp [h,hab,hac,had,hbc,hbd,hcd,Ne.symm hab,Ne.symm hac,Ne.symm had,
        Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_add_distrib]
  have hc (n : ℕ) : (∑ x ∈ S, if f x = n then v n else 0) =
      v n * (S.filter (fun x => f x = n)).card := by
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  rw [hc,hc,hc,hc]

end Atlas.Combinatorics
