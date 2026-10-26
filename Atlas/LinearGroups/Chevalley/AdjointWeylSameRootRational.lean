import Atlas.Algebra.WeylOperatorPinningTwo
import Atlas.LinearGroups.Chevalley.Integral.LoweringExponentialRational
import Atlas.LinearGroups.Chevalley.RankOne
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-! The actual rank-one Weyl word exchanges lowering and raising operators.
Only the integral same-node sl2 relations are used. Rational exponential
comparison is an intermediate; reduction to all rings is separate. -/
noncomputable section
namespace Atlas.Chevalley
open Integral
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The actual rank-one word takes F_i to -E_i over a rational algebra.
There is no irreducibility, non-G2, or simple-diamond hypothesis. -/
theorem adjointWeyl_one_conjugate_loweringOver_same_rat (i : b.support) :
    (adjointWeyl P b R i 1).val.val * loweringOver P b R i *
      ((adjointWeyl P b R i 1)⁻¹).val.val = -raisingOver P b R i := by
  let E := raisingOver P b R i
  let F := loweringOver P b R i
  let H := (Int.castRingHom R).mapMatrix (RootPairing.GeckConstruction.h i)
  have hEFint : raising P b i * lowering P b i -
      lowering P b i * raising P b i = RootPairing.GeckConstruction.h i := by
    simpa only [raising, lowering, Ring.lie_def] using
      (RootPairing.GeckConstruction.lie_e_f_same (b := b) i)
  have hHEint : RootPairing.GeckConstruction.h i * raising P b i -
      raising P b i * RootPairing.GeckConstruction.h i =
        raising P b i + raising P b i := by
    simpa only [raising, Ring.lie_def, b.cartanMatrix_apply_same, two_smul] using
      (RootPairing.GeckConstruction.lie_h_e (b := b) i i)
  have hHFint : RootPairing.GeckConstruction.h i * lowering P b i -
      lowering P b i * RootPairing.GeckConstruction.h i =
        -(lowering P b i + lowering P b i) := by
    simpa only [lowering, Ring.lie_def, b.cartanMatrix_apply_same,
      neg_smul, two_smul] using
      (RootPairing.GeckConstruction.lie_h_f (b := b) i i)
  have hEF : E * F - F * E = H := by
    have h := congrArg (Int.castRingHom R).mapMatrix hEFint
    simpa only [E, F, H, raisingOver, loweringOver, RingHom.mapMatrix_apply,
      map_sub, map_mul] using h
  have hHE : H * E - E * H = E + E := by
    have h := congrArg (Int.castRingHom R).mapMatrix hHEint
    simpa only [E, H, raisingOver, RingHom.mapMatrix_apply,
      map_sub, map_mul, map_add] using h
  have hHF : H * F - F * H = -(F + F) := by
    have h := congrArg (Int.castRingHom R).mapMatrix hHFint
    simpa only [F, H, loweringOver, RingHom.mapMatrix_apply,
      map_sub, map_mul, map_add, map_neg] using h
  have hEH : E * H - H * E = (-2 : ℚ) • E := by
    have h := congrArg Neg.neg hHE
    simpa only [neg_sub, neg_add, neg_smul, two_smul] using h
  have hFH : F * H - H * F = (2 : ℚ) • F := by
    have h := congrArg Neg.neg hHF
    simpa only [neg_sub, neg_neg, two_smul] using h
  have hED : Commute E ((-2 : ℚ) • E) := by
    change E * ((-2 : ℚ) • E) = ((-2 : ℚ) • E) * E
    rw [mul_smul_comm, smul_mul_assoc]
  have hFD : F * ((-2 : ℚ) • E) - ((-2 : ℚ) • E) * F =
      (2 : ℚ) • H := by
    calc
      F * ((-2 : ℚ) • E) - ((-2 : ℚ) • E) * F =
          (2 : ℚ) • (E * F - F * E) := by
        simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = (2 : ℚ) • H := by rw [hEF]
  have hpin := Atlas.Algebra.weyl_word_conjugate_operator_eq_half
    E F F H ((-2 : ℚ) • E)
    (raisingOver_nilpotent P b R i) (loweringOver_nilpotent P b R i)
    hEF hEH hED (Commute.refl F) hFH hFD
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
  change (adjointWeyl P b R i 1).val.val * F *
    ((adjointWeyl P b R i 1).val⁻¹).val = -E
  rw [hw]
  change (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E) * F *
    (IsNilpotent.exp (-E) * (IsNilpotent.exp F * IsNilpotent.exp (-E))) = -E
  calc
    _ = (1 / 2 : ℚ) • ((-2 : ℚ) • E) := by
      simpa only [mul_assoc] using hpin
    _ = -E := by module

/-- Rational exponential comparison gives the literal group identity. -/
theorem adjointWeyl_one_conjugate_Y_same_rat (i : b.support) (t : R) :
    adjointWeyl P b R i 1 * adjointY P b R i t *
      (adjointWeyl P b R i 1)⁻¹ = adjointX P b R i (-t) := by
  have h := IsNilpotent.exp_smul
    (ConjAct.toConjAct (adjointWeyl P b R i 1).val)
    ((loweringOver_nilpotent P b R i).smul t)
  change IsNilpotent.exp ((adjointWeyl P b R i 1).val.val *
      (t • loweringOver P b R i) * ((adjointWeyl P b R i 1)⁻¹).val.val) =
    (adjointWeyl P b R i 1).val.val * IsNilpotent.exp (t • loweringOver P b R i) *
      ((adjointWeyl P b R i 1)⁻¹).val.val at h
  rw [mul_smul_comm, smul_mul_assoc,
    adjointWeyl_one_conjugate_loweringOver_same_rat P b R i] at h
  apply Subtype.ext
  apply Units.ext
  change (adjointWeyl P b R i 1).val.val * (loweringRootElement P b R i t).val *
    ((adjointWeyl P b R i 1)⁻¹).val.val = raisingExponential P b R i (-t)
  rw [loweringRootElement_val, loweringExponential_eq_nilpotent_exp,
    raisingExponential_eq_nilpotent_exp]
  simpa only [smul_neg, neg_smul] using h.symm

end Atlas.Chevalley
