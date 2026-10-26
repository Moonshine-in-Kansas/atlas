import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Lean.Elab.Tactic.Omega

/-! Distinct simple roots have exactly the six ordered crystallographic
Cartan-pair possibilities. This uses the finite root-pairing classification,
not a classification of ranks, diagrams or groups. -/

namespace Atlas.Chevalley.RootData

variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The rank-two branch selector, including both multiple-edge orientations. -/
theorem cartanMatrix_pair_cases_of_ne (i j : b.support) (hij : i ≠ j) :
    (b.cartanMatrix i j = 0 ∧ b.cartanMatrix j i = 0) ∨
    (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) ∨
    (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -2) ∨
    (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -1) ∨
    (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -3) ∨
    (b.cartanMatrix i j = -3 ∧ b.cartanMatrix j i = -1) := by
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hroot : P.root i.val ≠ P.root j.val := P.root.injective.ne hne
  have hneg := b.root_ne_neg_of_ne i.property j.property hne
  have h := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'
    i.val j.val hroot hneg
  have hi := b.cartanMatrix_le_zero_of_ne i j hij
  have hj := b.cartanMatrix_le_zero_of_ne j i hij.symm
  change (b.cartanMatrix i j, b.cartanMatrix j i) ∈
    ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1),
      (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  omega

end Atlas.Chevalley.RootData
