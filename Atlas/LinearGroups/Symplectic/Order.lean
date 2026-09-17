import Atlas.LinearGroups.Symplectic.PairAction

noncomputable section
namespace Atlas.Symplectic

/-- Arithmetic recurrence matching the independent ordered-pair decomposition. -/
theorem orderNumerator_succ (n q : ℕ) :
    orderNumerator (n+1) q = (q^(2*(n+1))-1)*q^(2*n+1)*orderNumerator n q := by
  unfold orderNumerator
  rw [Finset.prod_range_succ]
  have h : (n+1)*(n+1) = (2*n+1)+n*n := by ring
  rw [h,pow_add]
  ring

/-- Full symplectic group order, uniform over every finite field and every rank. -/
theorem card_sp (n : ℕ) (F : Type*) [Field F] [Finite F] :
    Nat.card (Sp n F) = orderNumerator n (Nat.card F) := by
  induction n with
  | zero => rw [card_rank_zero,orderNumerator_zero]
  | succ n ih => rw [card_sp_succ,ih,orderNumerator_succ]

end Atlas.Symplectic
