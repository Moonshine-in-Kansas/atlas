import Atlas.Algebra.WeylOperatorPinningTwo
import Atlas.Algebra.DoubleEdgeExponential
import Atlas.LinearGroups.Chevalley.Integral.B2OperatorRelations
import Atlas.LinearGroups.Chevalley.A2WeylRational

/-! UNCOMPILED source candidate. The actual short/long double-edge Weyl
pinning and commutator over rational algebras. Integral descent is separate. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

private theorem isNilpotent_unit_conjugate
    {S : Type*} [Ring S] (u : Sˣ) (A : S) (hA : IsNilpotent A) :
    IsNilpotent (u.val * A * (u⁻¹).val) := by
  have h := hA.map
    (MulSemiringAction.toRingHom (ConjAct Sˣ) S (ConjAct.toConjAct u))
  change IsNilpotent (u.val * A * (u⁻¹).val) at h
  exact h

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- For i short and j long, the pinned short Weyl word sends E_j to
one half of [E_i,[E_i,E_j]]. This statement is only over rational algebras. -/
theorem adjointWeyl_one_conjugate_raisingOver_b2
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    (adjointWeyl P b R i 1).val.val * raisingOver P b R j *
      ((adjointWeyl P b R i 1)⁻¹).val.val =
        (1 / 2 : ℚ) •
          (raisingOver P b R i *
              (raisingOver P b R i * raisingOver P b R j -
                raisingOver P b R j * raisingOver P b R i) -
            (raisingOver P b R i * raisingOver P b R j -
              raisingOver P b R j * raisingOver P b R i) * raisingOver P b R i) := by
  let E := raisingOver P b R i
  let F := loweringOver P b R i
  let B := raisingOver P b R j
  let C := E * B - B * E
  let D := E * C - C * E
  obtain ⟨hED, _, _, _, hFC, hFD⟩ :=
    raisingOver_b2_operator_relations P b hdiamond R i j hne hij hji
  have hFB : Commute F B := by
    have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_lowering_commute_of_diamond P b hdiamond j i hne.symm).symm.eq
    simp only [map_mul] at h
    simpa only [F, B, raisingOver, loweringOver, RingHom.mapMatrix_apply,
      Commute, SemiconjBy] using h
  have hFCQ : F * C - C * F = (2 : ℚ) • B := by
    simpa only [two_smul] using hFC
  have hFDQ : F * D - D * F = (2 : ℚ) • C := by
    simpa only [two_smul] using hFD
  have hpin := Atlas.Algebra.weyl_word_conjugate_operator_eq_half E F B C D
    (raisingOver_nilpotent P b R i) (loweringOver_nilpotent P b R i)
    rfl rfl hED hFB hFCQ hFDQ
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
    ((adjointWeyl P b R i 1).val⁻¹).val = (1 / 2 : ℚ) • D
  rw [hw]
  change (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E) * B *
    (IsNilpotent.exp (-E) * (IsNilpotent.exp F * IsNilpotent.exp (-E))) = (1 / 2 : ℚ) • D
  simpa only [mul_assoc] using hpin

/-- The actual short Weyl word conjugates the long root exponential to
the exponential of the pinned twice-raised operator. -/
theorem adjointWeyl_one_conjugate_raisingExponential_b2
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (t : R) :
    (adjointWeyl P b R i 1).val.val * raisingExponential P b R j t *
      ((adjointWeyl P b R i 1)⁻¹).val.val =
        IsNilpotent.exp (t • ((1 / 2 : ℚ) •
          (raisingOver P b R i *
              (raisingOver P b R i * raisingOver P b R j -
                raisingOver P b R j * raisingOver P b R i) -
            (raisingOver P b R i * raisingOver P b R j -
              raisingOver P b R j * raisingOver P b R i) * raisingOver P b R i))) := by
  have h := IsNilpotent.exp_smul
    (ConjAct.toConjAct (adjointWeyl P b R i 1).val)
    ((raisingOver_nilpotent P b R j).smul t)
  change IsNilpotent.exp ((adjointWeyl P b R i 1).val.val *
      (t • raisingOver P b R j) * ((adjointWeyl P b R i 1)⁻¹).val.val) =
    (adjointWeyl P b R i 1).val.val * IsNilpotent.exp (t • raisingOver P b R j) *
      ((adjointWeyl P b R i 1)⁻¹).val.val at h
  rw [mul_smul_comm, smul_mul_assoc,
    adjointWeyl_one_conjugate_raisingOver_b2 P b hdiamond R i j hne hij hji] at h
  rw [← raisingExponential_eq_nilpotent_exp P b R j t] at h
  exact h.symm

/-- The actual mixed short/long root commutator, with the signs of the
installed C2 model. Every intermediate denominator lies in a rational algebra. -/
theorem adjointX_b2_commutator_eq_weyl_product_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (s t : R) :
    ⁅adjointX P b R i s, adjointX P b R j t⁆ =
      (adjointWeyl P b R j 1 * adjointX P b R i (-s*t) * (adjointWeyl P b R j 1)⁻¹) *
        (adjointWeyl P b R i 1 * adjointX P b R j (s^2*t) * (adjointWeyl P b R i 1)⁻¹) := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  obtain ⟨hAD, hBC, hBD, hCD, _, _⟩ :=
    raisingOver_b2_operator_relations P b hdiamond R i j hne hij hji
  have hCpin : (adjointWeyl P b R j 1).val.val * A *
      ((adjointWeyl P b R j 1)⁻¹).val.val = -C := by
    simpa only [A, B, C, neg_sub] using
      adjointWeyl_one_conjugate_raisingOver_a2 P b hdiamond R j i hne.symm hij
  have hDpin : (adjointWeyl P b R i 1).val.val * B *
      ((adjointWeyl P b R i 1)⁻¹).val.val = (1 / 2 : ℚ) • D :=
    adjointWeyl_one_conjugate_raisingOver_b2 P b hdiamond R i j hne hij hji
  have hCnil : IsNilpotent C := by
    have h := isNilpotent_unit_conjugate (adjointWeyl P b R j 1).val A
      (raisingOver_nilpotent P b R i)
    change IsNilpotent ((adjointWeyl P b R j 1).val.val * A *
      ((adjointWeyl P b R j 1)⁻¹).val.val) at h
    rw [hCpin] at h
    simpa only [neg_neg] using h.neg
  have hDnil : IsNilpotent ((1 / 2 : ℚ) • D) := by
    have h := isNilpotent_unit_conjugate (adjointWeyl P b R i 1).val B
      (raisingOver_nilpotent P b R j)
    change IsNilpotent ((adjointWeyl P b R i 1).val.val * B *
      ((adjointWeyl P b R i 1)⁻¹).val.val) at h
    rwa [hDpin] at h
  have hscaledAB : (s • A) * (t • B) - (t • B) * (s • A) = (s*t) • C := by
    dsimp only [C]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm t s, smul_sub]
  have hscaledAC : (s • A) * ((s*t) • C) - ((s*t) • C) * (s • A) =
      (s^2*t) • D := by
    calc
      (s • A) * ((s*t) • C) - ((s*t) • C) * (s • A) =
          (s*(s*t)) • (A*C-C*A) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (s*t) s, smul_sub]
      _ = (s^2*t) • D := by simp only [pow_two, mul_assoc, D]
  have hscaledDnil : IsNilpotent ((1 / 2 : ℚ) • ((s^2*t) • D)) := by
    have hcomm : (s^2*t) • ((1 / 2 : ℚ) • D) =
        (1 / 2 : ℚ) • ((s^2*t) • D) := smul_comm (s^2*t) (1 / 2 : ℚ) D
    rw [← hcomm]
    exact hDnil.smul (s^2*t)
  have hcalc := Atlas.Algebra.exp_doubleEdge_commutator
    (s • A) (t • B) ((s*t) • C) ((s^2*t) • D)
    ((raisingOver_nilpotent P b R i).smul s)
    ((raisingOver_nilpotent P b R j).smul t)
    (hCnil.smul (s*t)) hscaledDnil hscaledAB hscaledAC
    ((hAD.smul_left s).smul_right (s^2*t))
    ((hBC.smul_left t).smul_right (s*t))
    ((hBD.smul_left t).smul_right (s^2*t))
    ((hCD.smul_left (s*t)).smul_right (s^2*t))
  have hZ : (adjointWeyl P b R j 1).val.val * raisingExponential P b R i (-s*t) *
      ((adjointWeyl P b R j 1)⁻¹).val.val = IsNilpotent.exp ((s*t) • C) := by
    calc
      (adjointWeyl P b R j 1).val.val * raisingExponential P b R i (-s*t) *
          ((adjointWeyl P b R j 1)⁻¹).val.val =
          IsNilpotent.exp ((-s*t) • (B*A-A*B)) :=
        adjointWeyl_one_conjugate_raisingExponential_a2
          P b hdiamond R j i hne.symm hij (-s*t)
      _ = IsNilpotent.exp ((s*t) • C) := by
        have hneg : B*A-A*B = -C := by dsimp only [C]; abel
        simp only [hneg, neg_mul, neg_smul, smul_neg, neg_neg]
  have hW : (adjointWeyl P b R i 1).val.val * raisingExponential P b R j (s^2*t) *
      ((adjointWeyl P b R i 1)⁻¹).val.val =
        IsNilpotent.exp ((1 / 2 : ℚ) • ((s^2*t) • D)) := by
    have h := adjointWeyl_one_conjugate_raisingExponential_b2
      P b hdiamond R i j hne hij hji (s^2*t)
    change (adjointWeyl P b R i 1).val.val * raisingExponential P b R j (s^2*t) *
      ((adjointWeyl P b R i 1)⁻¹).val.val =
        IsNilpotent.exp ((s^2*t) • ((1 / 2 : ℚ) • D)) at h
    simpa only [smul_comm (s^2*t) (1 / 2 : ℚ) D] using h
  apply Subtype.ext
  apply Units.ext
  change raisingExponential P b R i s * raisingExponential P b R j t *
      raisingExponential P b R i (-s) * raisingExponential P b R j (-t) =
    ((adjointWeyl P b R j 1).val.val * raisingExponential P b R i (-s*t) *
      ((adjointWeyl P b R j 1)⁻¹).val.val) *
    ((adjointWeyl P b R i 1).val.val * raisingExponential P b R j (s^2*t) *
      ((adjointWeyl P b R i 1)⁻¹).val.val)
  rw [hZ, hW]
  simpa only [A, B, raisingExponential_eq_nilpotent_exp, neg_smul] using hcalc

end Atlas.Chevalley
