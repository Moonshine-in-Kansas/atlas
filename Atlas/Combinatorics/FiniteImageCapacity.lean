import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Atlas.Combinatorics
open scoped BigOperators

/-- The cardinal of an actual fiber agrees with its finite filter. -/
theorem fiber_card_filter {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (b : B) :
    Nat.card {a : A // f a=b} = (Finset.univ.filter (fun a => f a=b)).card := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

/-- A uniform fiber capacity bounds the cardinality through the actual image. -/
theorem card_le_capacity_mul_image {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (n : ℕ) (hb : ∀ b, Nat.card {a : A // f a=b} ≤ n) :
    Nat.card A ≤ n*(Finset.univ.image f).card := by
  classical
  have h := Finset.card_le_mul_card_image (f := f) Finset.univ n
    (fun b _ => by rw [← fiber_card_filter]; exact hb b)
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using h

/-- Saturating a uniform image capacity forces equality in every occupied fiber. -/
theorem fiber_eq_capacity_of_saturation {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (n : ℕ) (hb : ∀ b, Nat.card {a : A // f a=b} ≤ n)
    (ht : Nat.card A = n*(Finset.univ.image f).card)
    (b : B) (hmem : b ∈ Finset.univ.image f) : Nat.card {a : A // f a=b} = n := by
  classical
  have hs : (∑ c ∈ Finset.univ.image f, Nat.card {a : A // f a=c}) =
      ∑ _c ∈ Finset.univ.image f, n := by
    simp_rw [fiber_card_filter]
    rw [← Finset.card_eq_sum_card_image]
    simp only [Finset.card_univ, Finset.sum_const, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    simpa only [mul_comm, Nat.cast_id] using ht
  exact (Finset.sum_eq_sum_iff_of_le (fun c _ => hb c)).mp hs b hmem

end Atlas.Combinatorics
