import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite

/-! Cardinality interfaces for incidence counting inside finite pairwise-related sets. -/
namespace Atlas.Combinatorics
open scoped BigOperators

/-- Pairwise relatedness adds no constraint to subsets of a pairwise-related set. -/
theorem pairwise_subsets_card {α : Type*} (r : α→α→Prop) (s : Set α)
    (hs : s.Finite) (hp : s.Pairwise r) (n : ℕ) :
    Nat.card {t : Set α // t⊆s ∧ t.ncard=n ∧ t.Pairwise r}=s.ncard.choose n := by
  have he (t : Set α) : (t⊆s ∧ t.ncard=n ∧ t.Pairwise r) ↔ (t⊆s ∧ t.ncard=n) :=
    ⟨fun h=>⟨h.1,h.2.1⟩,fun h=>⟨h.1,h.2,hp.mono h.1⟩⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact Set.ncard_powerset_ncard hs n

/-- Ordered distinct points in a finite set, stated without a global finiteness assumption. -/
theorem ordered_distinct_card {α : Type*} (s : Set α) (hs : s.Finite) :
    Nat.card {z : s×s // z.1≠z.2}=s.ncard*(s.ncard-1) := by
  classical
  let : Finite s := hs.to_subtype
  let : Fintype s := Fintype.ofFinite s
  let e : {z : s×s // z.1≠z.2} ≃ Σx : s,{y : s // y≠x} :=
    {toFun := fun z=>⟨z.val.1,z.val.2,Ne.symm z.prop⟩
     invFun := fun z=>⟨(z.1,z.2.val),Ne.symm z.2.prop⟩
     left_inv := fun _=>rfl
     right_inv := fun _=>rfl}
  have hc (x : s) : Nat.card {y : s // y≠x}=s.ncard-1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique]
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [Nat.card_congr e,Nat.card_sigma]
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

end Atlas.Combinatorics
