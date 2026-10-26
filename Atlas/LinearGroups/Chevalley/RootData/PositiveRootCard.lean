import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.Data.Finset.Card

/-! Negation pairs the positive and nonpositive root labels of a finite
integral based root pairing. No Weyl-group or constructed-group premise. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base)

/-- The complement of the positive root set has the same size, by literal
root negation. The base supplies the positive/negative dichotomy. -/
theorem nonpositive_root_card_eq_positive :
    (Finset.univ.filter (fun β : ι => ¬ b.IsPos β)).card =
      (Finset.univ.filter (fun β : ι => b.IsPos β)).card := by
  letI := P.indexNeg
  let e : ι ≃ ι :=
    { toFun := fun β => -β
      invFun := fun β => -β
      left_inv := neg_neg
      right_inv := neg_neg }
  apply Finset.card_equiv e
  intro β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change ¬ b.IsPos β ↔ b.IsPos (-β)
  exact (RootPairing.Base.IsPos.neg_iff_not b β).symm

/-- Exactly half of the finite root labels are positive. This is a count
of the actual predicate b.IsPos, not of a separately specified positive list. -/
theorem card_root_eq_two_mul_card_positive :
    Fintype.card ι =
      2 * (Finset.univ.filter (fun β : ι => b.IsPos β)).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun β => b.IsPos β)
  rw [nonpositive_root_card_eq_positive P b] at h
  simpa only [Finset.card_univ, two_mul] using h.symm

end Atlas.Chevalley.RootData
