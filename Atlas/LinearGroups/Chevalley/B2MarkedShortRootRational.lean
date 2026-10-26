import Atlas.Algebra.WeylOperatorPinningMiddle
import Atlas.LinearGroups.Chevalley.B2WeylRational

/-! The signed marked B2 short-middle identity in the actual adjoint group.
Rational coefficients are used only in this intermediate operator calculation. -/
noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- For a short-long double edge, the short Weyl lift negates the middle
raising bracket. No inference from a root label is used. -/
theorem adjointWeyl_b2_negates_middle_bracket_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    (adjointWeyl P b R i 1).val.val *
        (raisingOver P b R i * raisingOver P b R j -
          raisingOver P b R j * raisingOver P b R i) *
        ((adjointWeyl P b R i 1)⁻¹).val.val =
      -(raisingOver P b R i * raisingOver P b R j -
        raisingOver P b R j * raisingOver P b R i) := by
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
  have hpin := Atlas.Algebra.weyl_word_conjugate_middle_eq_neg E F B C D
    (raisingOver_nilpotent P b R i) (loweringOver_nilpotent P b R i)
    rfl hED hFB hFCQ hFDQ
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
  change (adjointWeyl P b R i 1).val.val * C *
    ((adjointWeyl P b R i 1).val⁻¹).val = -C
  rw [hw]
  change (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E) * C *
    (IsNilpotent.exp (-E) * (IsNilpotent.exp F * IsNilpotent.exp (-E))) = -C
  simpa only [mul_assoc] using hpin

/-- If Z(t)=n_j X_i(t)n_j⁻¹, then n_i Z(t)n_i⁻¹=Z(-t).
The minus sign is retained before integral descent. -/
theorem adjointWeyl_b2_negates_short_conjugate_X_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (t : R) :
    adjointWeyl P b R i 1 *
        (adjointWeyl P b R j 1 * adjointX P b R i t * (adjointWeyl P b R j 1)⁻¹) *
        (adjointWeyl P b R i 1)⁻¹ =
      adjointWeyl P b R j 1 * adjointX P b R i (-t) * (adjointWeyl P b R j 1)⁻¹ := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let u := (adjointWeyl P b R i 1).val
  let v := (adjointWeyl P b R j 1).val
  have hpinC : u.val * C * (u⁻¹).val = -C :=
    adjointWeyl_b2_negates_middle_bracket_rat P b hdiamond R i j hne hij hji
  have hpinA : v.val * A * (v⁻¹).val = -C := by
    simpa only [v, A, B, C, neg_sub, Subgroup.coe_inv] using
      adjointWeyl_one_conjugate_raisingOver_a2 P b hdiamond R j i hne.symm hij
  have hnilC : IsNilpotent C := by
    have h := (raisingOver_nilpotent P b R i).map
      (MulSemiringAction.toRingHom
        (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
        (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct v))
    change IsNilpotent (v.val * A * (v⁻¹).val) at h
    rw [hpinA] at h
    simpa only [neg_neg] using h.neg
  have hroot (s : R) : v.val * raisingExponential P b R i s * (v⁻¹).val =
      IsNilpotent.exp ((-s) • C) := by
    have h := adjointWeyl_one_conjugate_raisingExponential_a2
      P b hdiamond R j i hne.symm hij s
    change v.val * raisingExponential P b R i s * (v⁻¹).val =
      IsNilpotent.exp (s • (B * A - A * B)) at h
    have hneg : B * A - A * B = -C := by dsimp only [C]; abel
    simpa only [hneg, smul_neg, neg_smul] using h
  have hexp : u.val * IsNilpotent.exp ((-t) • C) * (u⁻¹).val =
      IsNilpotent.exp (t • C) := by
    have h := IsNilpotent.exp_smul (ConjAct.toConjAct u) (hnilC.smul (-t))
    change IsNilpotent.exp (u.val * ((-t) • C) * (u⁻¹).val) =
      u.val * IsNilpotent.exp ((-t) • C) * (u⁻¹).val at h
    rw [mul_smul_comm, smul_mul_assoc, hpinC] at h
    simpa only [smul_neg, neg_smul, neg_neg] using h.symm
  apply Subtype.ext
  apply Units.ext
  change u.val * (v.val * raisingExponential P b R i t * (v⁻¹).val) * (u⁻¹).val =
    v.val * raisingExponential P b R i (-t) * (v⁻¹).val
  rw [hroot, hroot]
  simpa only [neg_neg] using hexp

end Atlas.Chevalley
