import Atlas.LinearGroups.Chevalley.Integral.RootString
import Atlas.LinearGroups.Chevalley.Integral.StringWeyl

/-! Identification of actual root-string reversal with the root reflection. -/
noncomputable section
namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

omit [P.IsReduced] in
theorem geckString_pairing (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j+1)) :
    P.pairingIn ℤ (geckStringIndex P i j h k) i =
      (k.val : ℤ) - (geckStringLength P i j-k.val : ℕ) := by
  have hc := P.chainBotCoeff_sub_chainTopCoeff
    (geckStringIndex_independent P i j h k)
  rw [geckStringIndex_bot P b i j h k, geckStringIndex_top P b i j h k] at hc
  exact hc.symm

omit [P.IsReduced] in
/-- Reversing the complete actual string is precisely the root reflection. -/
theorem geckStringIndex_rev (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j+1)) :
    geckStringIndex P i j h k.rev =
      P.reflectionPerm i (geckStringIndex P i j h k) := by
  apply P.root.injective
  rw [geckStringIndex_root, P.root_reflectionPerm, P.reflection_apply_root]
  have hp : P.pairing (geckStringIndex P i j h k) i =
      (k.val : ℤ) - (geckStringLength P i j-k.val : ℕ) := by
    rw [← P.algebraMap_pairingIn ℤ]
    simpa using geckString_pairing P b i j h k
  rw [hp, geckStringIndex_root]
  simp only [Fin.val_rev, Nat.add_sub_add_right]
  module

end Atlas.Chevalley.Integral
