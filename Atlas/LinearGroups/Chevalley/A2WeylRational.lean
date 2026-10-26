import Atlas.Algebra.WeylOperatorPinning
import Atlas.LinearGroups.Chevalley.Integral.LoweringExponentialRational
import Atlas.LinearGroups.Chevalley.Integral.A2LoweringBracket
import Atlas.LinearGroups.Chevalley.Integral.A2ExponentialRational
import Atlas.LinearGroups.Chevalley.RankOne
import Mathlib.GroupTheory.Commutator.Basic

/-! The actual pinned Weyl word and the single-edge raising bracket over
rational coefficient algebras. Integral polynomial descent is separate. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- The actual pinned Weyl representative sends E_j to [E_i,E_j]. -/
theorem adjointWeyl_one_conjugate_raisingOver_a2
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -1) :
    (adjointWeyl P b R i 1).val.val * raisingOver P b R j *
        ((adjointWeyl P b R i 1)⁻¹).val.val =
      raisingOver P b R i * raisingOver P b R j -
        raisingOver P b R j * raisingOver P b R i := by
  let E := raisingOver P b R i
  let F := loweringOver P b R i
  let B := raisingOver P b R j
  let C := E * B - B * E
  have hEC : Commute E C := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_a2_commute_bracket_left P b hdiamond i j hne hji).eq
    simp only [map_mul, map_sub] at h
    simpa only [E, C, B, raisingOver, RingHom.mapMatrix_apply, Commute, SemiconjBy] using h
  have hFB : Commute F B := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
    simp only [map_mul] at h
    simpa only [F, B, raisingOver, loweringOver, RingHom.mapMatrix_apply,
      Commute, SemiconjBy] using h
  have hFC : F * C - C * F = B :=
    loweringOver_a2_bracket_eq_raising P b hdiamond R i j hne hji
  have hpin := Atlas.Algebra.weyl_word_conjugate_operator_eq E F B C
    (raisingOver_nilpotent P b R i) (loweringOver_nilpotent P b R i)
    rfl hEC hFB hFC
  let e : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
    ⟨IsNilpotent.exp E, IsNilpotent.exp (-E),
      IsNilpotent.exp_mul_exp_neg_self (raisingOver_nilpotent P b R i),
      IsNilpotent.exp_neg_mul_exp_self (raisingOver_nilpotent P b R i)⟩
  let f : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
    ⟨IsNilpotent.exp F, IsNilpotent.exp (-F),
      IsNilpotent.exp_mul_exp_neg_self (loweringOver_nilpotent P b R i),
      IsNilpotent.exp_neg_mul_exp_self (loweringOver_nilpotent P b R i)⟩
  have hw : (adjointWeyl P b R i 1).val = e * f⁻¹ * e := by
    apply Units.ext
    change raisingExponential P b R i 1 * (loweringRootElement P b R i (-1)).val *
        raisingExponential P b R i 1 =
      IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
    simp only [E, F, loweringRootElement_val, raisingExponential_eq_nilpotent_exp,
      loweringExponential_eq_nilpotent_exp, one_smul, neg_one_smul]
  change (adjointWeyl P b R i 1).val.val * B *
    ((adjointWeyl P b R i 1).val⁻¹).val = C
  rw [hw]
  change (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E) * B *
    (IsNilpotent.exp (-E) * (IsNilpotent.exp F * IsNilpotent.exp (-E))) = C
  simpa only [mul_assoc] using hpin

/-- Conjugating the actual root exponential by the pinned Weyl word
gives the exponential of the actual adjacent bracket. -/
theorem adjointWeyl_one_conjugate_raisingExponential_a2
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -1) (t : R) :
    (adjointWeyl P b R i 1).val.val * raisingExponential P b R j t *
        ((adjointWeyl P b R i 1)⁻¹).val.val =
      IsNilpotent.exp (t • (raisingOver P b R i * raisingOver P b R j -
        raisingOver P b R j * raisingOver P b R i)) := by
  have h := IsNilpotent.exp_smul
    (ConjAct.toConjAct (adjointWeyl P b R i 1).val)
    ((raisingOver_nilpotent P b R j).smul t)
  change IsNilpotent.exp ((adjointWeyl P b R i 1).val.val *
      (t • raisingOver P b R j) * ((adjointWeyl P b R i 1)⁻¹).val.val) =
    (adjointWeyl P b R i 1).val.val * IsNilpotent.exp (t • raisingOver P b R j) *
      ((adjointWeyl P b R i 1)⁻¹).val.val at h
  rw [mul_smul_comm, smul_mul_assoc,
    adjointWeyl_one_conjugate_raisingOver_a2 P b hdiamond R i j hne hji] at h
  rw [← raisingExponential_eq_nilpotent_exp P b R j t] at h
  exact h.symm

/-- The A2 commutator at (1,t) is a conjugate in the actual generated group. -/
theorem adjointX_a2_commutator_one_eq_weyl_conjugate_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    ⁅adjointX P b R i 1, adjointX P b R j t⁆ =
      adjointWeyl P b R i 1 * adjointX P b R j t * (adjointWeyl P b R i 1)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change raisingExponential P b R i 1 * raisingExponential P b R j t *
      raisingExponential P b R i (-1) * raisingExponential P b R j (-t) =
    (adjointWeyl P b R i 1).val.val * raisingExponential P b R j t *
      ((adjointWeyl P b R i 1)⁻¹).val.val
  rw [raisingExponential_a2_commutator_eq_exp P b hdiamond R i j hne hij hji,
    one_mul]
  exact (adjointWeyl_one_conjugate_raisingExponential_a2
    P b hdiamond R i j hne hji t).symm

end Atlas.Chevalley
