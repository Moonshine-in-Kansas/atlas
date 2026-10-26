import Atlas.Algebra.WeylOperatorPinningHighest
import Atlas.LinearGroups.Chevalley.B2WeylRational
import Mathlib.Tactic.NoncommRing

/-! A first marked B2 transport identity for the actual adjoint group.
The rational coefficient hypothesis is explicit. Integral descent and the
independent minuscule blocks are not claimed in this module. -/
noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- The other end of the actual single-edge operator string. Only the
indicated Cartan entry is needed, so this also applies to the long side of B2. -/
theorem adjointWeyl_one_conjugate_raisingBracket_highest
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -1) :
    (adjointWeyl P b R i 1).val.val *
        (raisingOver P b R i * raisingOver P b R j -
          raisingOver P b R j * raisingOver P b R i) *
        ((adjointWeyl P b R i 1)⁻¹).val.val = -raisingOver P b R j := by
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
  have hpin := Atlas.Algebra.weyl_word_conjugate_highest_eq_neg E F B C
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
  change (adjointWeyl P b R i 1).val.val * C *
    ((adjointWeyl P b R i 1).val⁻¹).val = -B
  rw [hw]
  change (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E) * C *
    (IsNilpotent.exp (-E) * (IsNilpotent.exp F * IsNilpotent.exp (-E))) = -B
  simpa only [mul_assoc] using hpin

/-- At a double edge, the long simple Weyl element fixes the twice-raised
operator. This is an operator calculation, not an inference from its root label. -/
theorem adjointWeyl_b2_fixes_double_bracket_rat
    (i j : b.support) (hne : i ≠ j) (hij : b.cartanMatrix i j = -1) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let D := A * C - C * A
    (adjointWeyl P b R j 1).val.val * D *
      ((adjointWeyl P b R j 1)⁻¹).val.val = D := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let u := (adjointWeyl P b R j 1).val
  let f := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct u)
  have hmapA : f A = -C := by
    change u.val * A * (u⁻¹).val = -C
    have h := adjointWeyl_one_conjugate_raisingOver_a2 P b hdiamond R j i hne.symm hij
    change u.val * A * (u⁻¹).val = B * A - A * B at h
    simpa only [C, neg_sub] using h
  have hmapC : f C = A := by
    have h := adjointWeyl_one_conjugate_raisingBracket_highest
      P b hdiamond R j i hne.symm hij
    change u.val * (B * A - A * B) * (u⁻¹).val = -A at h
    have hneg : B * A - A * B = -C := by dsimp only [C]; abel
    rw [hneg, mul_neg, neg_mul] at h
    exact neg_injective h
  have hmapD : f D = D := by
    change f (A * C - C * A) = A * C - C * A
    rw [map_sub, map_mul, map_mul, hmapA, hmapC]
    noncomm_ring
  exact hmapD

/-- The actual long-root family n_i X_j(t) n_i^{-1} is fixed by n_j.
Here i is short and j is long. This is one marked middle-root identity of
the length-four braid, currently over rational algebras only. -/
theorem adjointWeyl_b2_fixes_long_conjugate_X_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (t : R) :
    adjointWeyl P b R j 1 *
        (adjointWeyl P b R i 1 * adjointX P b R j t *
          (adjointWeyl P b R i 1)⁻¹) * (adjointWeyl P b R j 1)⁻¹ =
      adjointWeyl P b R i 1 * adjointX P b R j t * (adjointWeyl P b R i 1)⁻¹ := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let Q := (1 / 2 : ℚ) • D
  let u := (adjointWeyl P b R j 1).val
  let v := (adjointWeyl P b R i 1).val
  have hpin : v.val * B * (v⁻¹).val = Q :=
    adjointWeyl_one_conjugate_raisingOver_b2 P b hdiamond R i j hne hij hji
  have hnil : IsNilpotent Q := by
    have h := (raisingOver_nilpotent P b R j).map
      (MulSemiringAction.toRingHom
        (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
        (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct v))
    change IsNilpotent (v.val * B * (v⁻¹).val) at h
    rwa [hpin] at h
  have hfixedD : u.val * D * (u⁻¹).val = D :=
    adjointWeyl_b2_fixes_double_bracket_rat P b hdiamond R i j hne hij
  have hfixedQ : u.val * Q * (u⁻¹).val = Q := by
    change u.val * ((1 / 2 : ℚ) • D) * (u⁻¹).val = (1 / 2 : ℚ) • D
    rw [mul_smul_comm, smul_mul_assoc, hfixedD]
  have hfixedExp : u.val * IsNilpotent.exp (t • Q) * (u⁻¹).val =
      IsNilpotent.exp (t • Q) := by
    have h := IsNilpotent.exp_smul (ConjAct.toConjAct u) (hnil.smul t)
    change IsNilpotent.exp (u.val * (t • Q) * (u⁻¹).val) =
      u.val * IsNilpotent.exp (t • Q) * (u⁻¹).val at h
    rw [mul_smul_comm, smul_mul_assoc, hfixedQ] at h
    exact h.symm
  have hroot : v.val * raisingExponential P b R j t * (v⁻¹).val =
      IsNilpotent.exp (t • Q) :=
    adjointWeyl_one_conjugate_raisingExponential_b2 P b hdiamond R i j hne hij hji t
  apply Subtype.ext
  apply Units.ext
  change u.val * (v.val * raisingExponential P b R j t * (v⁻¹).val) * (u⁻¹).val =
    v.val * raisingExponential P b R j t * (v⁻¹).val
  rw [hroot]
  exact hfixedExp

end Atlas.Chevalley
