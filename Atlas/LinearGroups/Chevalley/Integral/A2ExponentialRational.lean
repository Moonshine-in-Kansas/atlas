import Atlas.Algebra.TwoStepExponential
import Atlas.LinearGroups.Chevalley.Integral.GeckExponentialRational
import Atlas.LinearGroups.Chevalley.Integral.A2IntegralSerre
import Atlas.LinearGroups.Chevalley.Integral.A2BracketNilpotent

/-! Source-only candidate: the actual single-edge Geck root commutator over
a rational coefficient algebra. Integral polynomial descent is separate. -/
noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- The bracket and its nilpotence are derived from the actual integral
operators. Only the generic diamond premise remains explicit here. -/
theorem raisingExponential_a2_commutator_eq_exp
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1)
    (s t : R) :
    raisingExponential P b R i s * raisingExponential P b R j t *
        raisingExponential P b R i (-s) * raisingExponential P b R j (-t) =
      IsNilpotent.exp ((s*t) •
        (raisingOver P b R i * raisingOver P b R j -
          raisingOver P b R j * raisingOver P b R i)) := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A*B-B*A
  have hscaled : (s • A) * (t • B) - (t • B) * (s • A) = (s*t) • C := by
    dsimp only [C]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm t s, smul_sub]
  have hcomm : Commute A C ∧ Commute B C :=
    raisingOver_a2_commute_bracket P b hdiamond R i j hne hij hji
  have hnil : IsNilpotent C := raisingOver_a2_bracket_isNilpotent P b R i j hij hji
  have h := Atlas.Algebra.exp_commutator_eq_exp_bracket (s • A) (t • B)
    ((raisingOver_nilpotent P b R i).smul s)
    ((raisingOver_nilpotent P b R j).smul t)
    (by rw [hscaled]; exact hnil.smul (s*t))
    (by rw [hscaled]; exact (hcomm.1.smul_left s).smul_right (s*t))
    (by rw [hscaled]; exact (hcomm.2.smul_left t).smul_right (s*t))
  simpa only [raisingExponential_eq_nilpotent_exp, neg_smul, hscaled] using h

end Atlas.Chevalley.Integral
