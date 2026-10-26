import Atlas.LinearGroups.Chevalley.Integral.GeckExponentialRational
import Mathlib.Algebra.Ring.Action.ConjAct

/-! The rational lowering exponential comparison, obtained from the existing
integral opposition conjugation and the raising comparison. -/

noncomputable section

namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The actual integral lowering exponential agrees with the algebraic
exponential over a rational coefficient algebra. -/
theorem loweringExponential_eq_nilpotent_exp (i : b.support) (t : R) :
    loweringExponential P b R i t =
      IsNilpotent.exp (t • loweringOver P b R i) := by
  have hconj := IsNilpotent.exp_smul
    (ConjAct.toConjAct (oppositionUnit P b R))
    ((raisingOver_nilpotent P b R i).smul t)
  change IsNilpotent.exp
      (oppositionOver P b R * (t • raisingOver P b R i) * oppositionOver P b R) =
    oppositionOver P b R * IsNilpotent.exp (t • raisingOver P b R i) *
      oppositionOver P b R at hconj
  rw [mul_smul_comm, smul_mul_assoc, oppositionOver_raisingOver P b R i] at hconj
  calc
    loweringExponential P b R i t = (loweringRootElement P b R i t).val :=
      (loweringRootElement_val P b R i t).symm
    _ = oppositionOver P b R * raisingExponential P b R i t *
        oppositionOver P b R := rfl
    _ = oppositionOver P b R * IsNilpotent.exp (t • raisingOver P b R i) *
        oppositionOver P b R := by
      rw [raisingExponential_eq_nilpotent_exp P b R i t]
    _ = IsNilpotent.exp (t • loweringOver P b R i) := hconj.symm

end Atlas.Chevalley.Integral
