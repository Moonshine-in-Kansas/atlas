import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-! Elementary scaling commutators, independent of any group family. -/
namespace Atlas.GroupTheory
open scoped commutatorElement
variable {K G : Type*} [Field K] [Group G]

/-- A conjugation which scales an additive root parameter produces its difference. -/
theorem scaling_commutator (x : Multiplicative K →* G) (h : G) (c : K)
    (hc : ∀ u : K, h * x (Multiplicative.ofAdd u) * h⁻¹ =
      x (Multiplicative.ofAdd (c*u))) (u : K) :
    ⁅h, x (Multiplicative.ofAdd u)⁆ = x (Multiplicative.ofAdd ((c-1)*u)) := by
  rw [commutatorElement_def, hc, ← map_inv, ← map_mul]
  congr 1
  change c*u + -u = (c-1)*u
  ring

/-- Every parameter is a commutator when the scaling factor differs from one. -/
theorem scaled_root_mem_commutator (x : Multiplicative K →* G) (h : G) (c : K)
    (hne : c ≠ 1)
    (hc : ∀ u : K, h * x (Multiplicative.ofAdd u) * h⁻¹ =
      x (Multiplicative.ofAdd (c*u))) (t : K) :
    x (Multiplicative.ofAdd t) ∈ commutator G := by
  have ht : (c-1)*(t/(c-1)) = t := by
    field_simp [sub_ne_zero.mpr hne]
  rw [← ht, ← scaling_commutator x h c hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Finite fields of size greater than three contain a nonscalar-square unit. -/
theorem exists_nonzero_sq_ne_one [Fintype K] (hq : 3 < Fintype.card K) :
    ∃ a : K, a ≠ 0 ∧ a^2 ≠ 1 := by
  classical
  by_contra! h
  have hsub : (Finset.univ : Finset K) ⊆ {0,1,-1} := by
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hs := (sq_eq_one_iff.mp (h a ha0))
      rcases hs with hs | hs <;> simp [hs]
  have hcard := Finset.card_le_card hsub
  have hbound : ({0,1,-1} : Finset K).card ≤ 3 := by
    calc
      _ ≤ ({1,-1} : Finset K).card + 1 := Finset.card_insert_le _ _
      _ ≤ 3 := by
        have := Finset.card_insert_le (1 : K) ({-1} : Finset K)
        simp only [Finset.card_singleton] at this
        omega
  simp only [Finset.card_univ] at hcard
  omega

end Atlas.GroupTheory
