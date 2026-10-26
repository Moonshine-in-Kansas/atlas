import Atlas.Algebra.WeylOperatorPinningThreeMiddle
import Atlas.LinearGroups.Chevalley.G2WeylRational
import Atlas.LinearGroups.Chevalley.B2MarkedLongRootRational

/-! Two marked middle-root operator identities in the actual G2 pair.
Rational algebra assumptions are explicit here; integral transfer is separate.
The argument uses operator strings, never root-label coincidence alone. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]
include hdiamond

theorem adjointWeyl_g2_conjugate_middle_operators
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = -3) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let D := A * C - C * A
    let u := (adjointWeyl P b R i 1).val
    u.val * C * (u⁻¹).val = (-1 / 2 : ℚ) • D ∧
      u.val * D * (u⁻¹).val = (2 : ℚ) • C := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let F := loweringOver P b R i
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  obtain ⟨hAL, hFB, hFC, hFD, hFL⟩ :=
    raisingOver_g2_weyl_string P b hdiamond R i j hne hji
  have hFCQ : F * C - C * F = (3 : ℚ) • B := by
    calc
      _ = (3 : ℤ) • B := hFC
      _ = (3 : ℚ) • B := by
        simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℚ (3 : ℤ) B).symm
  have hFDQ : F * D - D * F = (4 : ℚ) • C := by
    calc
      _ = (4 : ℤ) • C := hFD
      _ = (4 : ℚ) • C := by
        simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℚ (4 : ℤ) C).symm
  have hFLQ : F * L - L * F = (3 : ℚ) • D := by
    calc
      _ = (3 : ℤ) • D := hFL
      _ = (3 : ℚ) • D := by
        simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℚ (3 : ℤ) D).symm
  have hp := Atlas.Algebra.weyl_word_conjugate_middle_three A F B C D L
    (raisingOver_nilpotent P b R i) (loweringOver_nilpotent P b R i)
    rfl rfl hAL hFB hFCQ hFDQ hFLQ
  let e : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
    ⟨IsNilpotent.exp A, IsNilpotent.exp (-A),
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
      IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A
    simp only [A, F, loweringRootElement_val, raisingExponential_eq_nilpotent_exp,
      loweringExponential_eq_nilpotent_exp, one_smul, neg_one_smul]
  change
    (adjointWeyl P b R i 1).val.val * C *
        ((adjointWeyl P b R i 1).val⁻¹).val = (-1 / 2 : ℚ) • D ∧
      (adjointWeyl P b R i 1).val.val * D *
        ((adjointWeyl P b R i 1).val⁻¹).val = (2 : ℚ) • C
  rw [hw]
  change
    (IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A) * C *
        (IsNilpotent.exp (-A) * (IsNilpotent.exp F * IsNilpotent.exp (-A))) =
          (-1 / 2 : ℚ) • D ∧
      (IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A) * D *
        (IsNilpotent.exp (-A) * (IsNilpotent.exp F * IsNilpotent.exp (-A))) =
          (2 : ℚ) • C
  simpa only [mul_assoc] using hp

private theorem reverse_short_string
    (i j : b.support) (hne : i ≠ j) (hij : b.cartanMatrix i j = -1) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let u := (adjointWeyl P b R j 1).val
    u.val * A * (u⁻¹).val = -C ∧ u.val * C * (u⁻¹).val = A := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let u := (adjointWeyl P b R j 1).val
  constructor
  · have h := adjointWeyl_one_conjugate_raisingOver_a2 P b hdiamond R j i hne.symm hij
    change u.val * A * (u⁻¹).val = B * A - A * B at h
    simpa only [C, neg_sub] using h
  · have h := adjointWeyl_one_conjugate_raisingBracket_highest
      P b hdiamond R j i hne.symm hij
    change u.val * (B * A - A * B) * (u⁻¹).val = -A at h
    have hneg : B * A - A * B = -C := by dsimp only [C]; abel
    rw [hneg, mul_neg, neg_mul] at h
    exact neg_injective h

/-- n_j fixes the actual short middle operator represented by n_i n_j.
This is a concrete equality of matrices, not an inference from its root label. -/
theorem adjointWeyl_g2_fixes_short_middle_operator_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let u := (adjointWeyl P b R j 1).val
    let v := (adjointWeyl P b R i 1 * adjointWeyl P b R j 1).val
    u.val * (v.val * raisingOver P b R i * (v⁻¹).val) * (u⁻¹).val =
      v.val * raisingOver P b R i * (v⁻¹).val := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let ni := (adjointWeyl P b R i 1).val
  let nj := (adjointWeyl P b R j 1).val
  let fi := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct ni)
  let fj := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct nj)
  obtain ⟨hja, hjc⟩ := reverse_short_string P b hdiamond R i j hne hij
  obtain ⟨hic, hid⟩ := adjointWeyl_g2_conjugate_middle_operators P b hdiamond R i j hne hji
  have hpin : fi (fj A) = (1 / 2 : ℚ) • D := by
    change fi (nj.val * A * (nj⁻¹).val) = _
    rw [hja, map_neg]
    change -(ni.val * C * (ni⁻¹).val) = _
    rw [hic]
    module
  have hfixed : fj D = D := by
    change fj (A * C - C * A) = A * C - C * A
    rw [map_sub, map_mul, map_mul]
    change (nj.val * A * (nj⁻¹).val) * (nj.val * C * (nj⁻¹).val) -
      (nj.val * C * (nj⁻¹).val) * (nj.val * A * (nj⁻¹).val) = _
    rw [hja, hjc]
    change (-C) * A - A * (-C) = A * C - C * A
    simp only [neg_mul, mul_neg]
    abel
  have h : fj (fi (fj A)) = fi (fj A) := by
    rw [hpin]
    change nj.val * ((1 / 2 : ℚ) • D) * (nj⁻¹).val = (1 / 2 : ℚ) • D
    rw [mul_smul_comm, smul_mul_assoc]
    exact congrArg (fun x => (1 / 2 : ℚ) • x) hfixed
  change nj.val * (ni.val * (nj.val * A * (nj⁻¹).val) * (ni⁻¹).val) * (nj⁻¹).val =
    ni.val * (nj.val * A * (nj⁻¹).val) * (ni⁻¹).val at h
  change nj.val * ((ni * nj).val * A * ((ni * nj)⁻¹).val) * (nj⁻¹).val =
    (ni * nj).val * A * ((ni * nj)⁻¹).val
  simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using h

/-- n_i fixes the actual long middle operator represented by n_j n_i.
Its operator is minus [C,D]/6; only this rational intermediate uses division. -/
theorem adjointWeyl_g2_fixes_long_middle_operator_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let u := (adjointWeyl P b R i 1).val
    let v := (adjointWeyl P b R j 1 * adjointWeyl P b R i 1).val
    u.val * (v.val * raisingOver P b R j * (v⁻¹).val) * (u⁻¹).val =
      v.val * raisingOver P b R j * (v⁻¹).val := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  let ni := (adjointWeyl P b R i 1).val
  let nj := (adjointWeyl P b R j 1).val
  let fi := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct ni)
  let fj := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct nj)
  obtain ⟨hja, hjc⟩ := reverse_short_string P b hdiamond R i j hne hij
  obtain ⟨hic, hid⟩ := adjointWeyl_g2_conjugate_middle_operators P b hdiamond R i j hne hji
  have hjd : fj D = D := by
    change fj (A * C - C * A) = A * C - C * A
    rw [map_sub, map_mul, map_mul]
    change (nj.val * A * (nj⁻¹).val) * (nj.val * C * (nj⁻¹).val) -
      (nj.val * C * (nj⁻¹).val) * (nj.val * A * (nj⁻¹).val) = _
    rw [hja, hjc]
    change (-C) * A - A * (-C) = A * C - C * A
    simp only [neg_mul, mul_neg]
    abel
  have hjl : fj L = -(C * D - D * C) := by
    change fj (A * D - D * A) = _
    rw [map_sub, map_mul, map_mul, hjd]
    change (nj.val * A * (nj⁻¹).val) * D - D * (nj.val * A * (nj⁻¹).val) = _
    rw [hja]
    change (-C) * D - D * (-C) = -(C * D - D * C)
    simp only [neg_mul, mul_neg]
    abel
  have hpin : fj (fi B) = (-1 / 6 : ℚ) • (C * D - D * C) := by
    change fj (ni.val * B * (ni⁻¹).val) = _
    have hib : ni.val * B * (ni⁻¹).val = (1 / 6 : ℚ) • L :=
      adjointWeyl_one_conjugate_raisingOver_g2 P b hdiamond R i j hne hji
    rw [hib]
    change nj.val * ((1 / 6 : ℚ) • L) * (nj⁻¹).val = _
    rw [mul_smul_comm, smul_mul_assoc]
    change (1 / 6 : ℚ) • fj L = _
    rw [hjl]
    module
  have hfixed : fi (C * D - D * C) = C * D - D * C := by
    rw [map_sub, map_mul, map_mul]
    change (ni.val * C * (ni⁻¹).val) * (ni.val * D * (ni⁻¹).val) -
      (ni.val * D * (ni⁻¹).val) * (ni.val * C * (ni⁻¹).val) = _
    rw [hic, hid]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  have h : fi (fj (fi B)) = fj (fi B) := by
    rw [hpin]
    change ni.val * ((-1 / 6 : ℚ) • (C * D - D * C)) * (ni⁻¹).val = _
    rw [mul_smul_comm, smul_mul_assoc]
    exact congrArg (fun x => (-1 / 6 : ℚ) • x) hfixed
  change ni.val * (nj.val * (ni.val * B * (ni⁻¹).val) * (nj⁻¹).val) * (ni⁻¹).val =
    nj.val * (ni.val * B * (ni⁻¹).val) * (nj⁻¹).val at h
  change ni.val * ((nj * ni).val * B * ((nj * ni)⁻¹).val) * (ni⁻¹).val =
    (nj * ni).val * B * ((nj * ni)⁻¹).val
  simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using h

end Atlas.Chevalley
