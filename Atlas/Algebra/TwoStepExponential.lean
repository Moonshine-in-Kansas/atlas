import Atlas.Algebra.FiniteHadamard
import Mathlib.Algebra.Ring.Action.ConjAct

/-! The finite exponential commutator identity for a nilpotent two-step
associative Lie configuration. All three nilpotence hypotheses are explicit. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- If A, B and C=AB−BA are nilpotent and C commutes with A and B, then
the group commutator exp(A)exp(B)exp(−A)exp(−B) equals exp(C). -/
theorem exp_commutator_eq_exp_bracket
    (A B : S) (hA : IsNilpotent A) (hB : IsNilpotent B)
    (hC : IsNilpotent (A * B - B * A))
    (hAC : Commute A (A * B - B * A))
    (hBC : Commute B (A * B - B * A)) :
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) *
        IsNilpotent.exp (-B) = IsNilpotent.exp (A * B - B * A) := by
  let u : Sˣ :=
    ⟨IsNilpotent.exp A, IsNilpotent.exp (-A),
      IsNilpotent.exp_mul_exp_neg_self hA, IsNilpotent.exp_neg_mul_exp_self hA⟩
  have hmap := IsNilpotent.exp_smul (ConjAct.toConjAct u) hB
  change IsNilpotent.exp (IsNilpotent.exp A * B * IsNilpotent.exp (-A)) =
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) at hmap
  rw [exp_mul_mul_exp_neg_eq_add_bracket A B hA hAC] at hmap
  rw [← hmap, add_comm B (A * B - B * A),
    IsNilpotent.exp_add_of_commute hBC.symm hC hB, mul_assoc,
    IsNilpotent.exp_mul_exp_neg_self hB, mul_one]

end Atlas.Algebra
