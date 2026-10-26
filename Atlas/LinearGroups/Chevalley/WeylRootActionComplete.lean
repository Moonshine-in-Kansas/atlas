import Atlas.LinearGroups.Chevalley.WeylRootAction

/-! The pinned unit-parameter Weyl word on every actual Geck root coordinate.
These are basis-vector formulas, not conjugation formulas for root operators.
The opposite simple-root columns have positive coefficient in this basis. -/

noncomputable section
open scoped Matrix
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- A single exact signed-reflection formula, including both parallel roots.
The chain coefficient is zero on parallel pairs, where the actual sign is +1. -/
theorem adjointWeyl_one_root_signed (i : b.support) (j : ι) :
    (adjointWeyl P b R i 1).val.val *ᵥ rootVector P b R j =
      (-1 : R) ^ P.chainBotCoeff i j •
        rootVector P b R (P.reflectionPerm i j) := by
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · simpa using adjointWeyl_root_independent P b R i j h 1
  · rw [P.chainBotCoeff_of_not_linearIndependent h, pow_zero, one_smul]
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j h with hp | hn
    · have hj : j = i := (P.root.injective hp).symm
      subst j
      simpa only [Units.inv_eq_val_inv, inv_one, Units.val_one, one_pow,
        one_smul, RootPairing.indexNeg_neg] using adjointWeyl_positive P b R i 1
    · have hj : j = P.reflectionPerm i i := by
        apply P.root_eq_neg_iff.mp
        simpa only [neg_neg] using congrArg Neg.neg hn.symm
      subst j
      simpa only [Units.val_one, one_pow, one_smul, RootPairing.indexNeg_neg,
        P.reflectionPerm_self] using adjointWeyl_negative P b R i 1

end Atlas.Chevalley
