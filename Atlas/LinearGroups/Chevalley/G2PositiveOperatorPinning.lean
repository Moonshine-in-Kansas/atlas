import Atlas.LinearGroups.Chevalley.G2MarkedMiddleOperatorsRational
import Atlas.LinearGroups.Chevalley.Integral.G2CrossBrackets

/-! Source candidate: pin the four composite positive-root operators in a
triple edge to the literal installed Weyl words. Rational coefficients are
explicit. This is not a commutator factorization or an all-ring transfer. -/

noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

include hdiamond

/-- In increasing root height, the four actual pinned operators are
`-C`, `D/2`, `L/6`, `F/6`; their Weyl words are `j`, `ij`, `i`, `ji`. -/
theorem adjointWeyl_g2_positive_operator_pinnings
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let D := A * C - C * A
    let L := A * D - D * A
    let F := B * L - L * B
    let ni := (adjointWeyl P b R i 1).val
    let nj := (adjointWeyl P b R j 1).val
    nj.val * A * (nj⁻¹).val = -C ∧
      (ni * nj).val * A * ((ni * nj)⁻¹).val = (1 / 2 : ℚ) • D ∧
      ni.val * B * (ni⁻¹).val = (1 / 6 : ℚ) • L ∧
      (nj * ni).val * B * ((nj * ni)⁻¹).val = (1 / 6 : ℚ) • F := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  let F := B * L - L * B
  let ni := (adjointWeyl P b R i 1).val
  let nj := (adjointWeyl P b R j 1).val
  let fi := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct ni)
  let fj := MulSemiringAction.toRingHom
    (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct nj)
  change nj.val * A * (nj⁻¹).val = -C ∧
    (ni * nj).val * A * ((ni * nj)⁻¹).val = (1 / 2 : ℚ) • D ∧
    ni.val * B * (ni⁻¹).val = (1 / 6 : ℚ) • L ∧
    (nj * ni).val * B * ((nj * ni)⁻¹).val = (1 / 6 : ℚ) • F
  have hja : nj.val * A * (nj⁻¹).val = -C := by
    have h := adjointWeyl_one_conjugate_raisingOver_a2 P b hdiamond R j i hne.symm hij
    change nj.val * A * (nj⁻¹).val = B * A - A * B at h
    simpa only [C, neg_sub] using h
  obtain ⟨hic, _⟩ :=
    adjointWeyl_g2_conjugate_middle_operators P b hdiamond R i j hne hji
  have hshort : fi (fj A) = (1 / 2 : ℚ) • D := by
    change fi (nj.val * A * (nj⁻¹).val) = _
    rw [hja, map_neg]
    change -(ni.val * C * (ni⁻¹).val) = _
    rw [hic]
    module
  have hib : ni.val * B * (ni⁻¹).val = (1 / 6 : ℚ) • L :=
    adjointWeyl_one_conjugate_raisingOver_g2 P b hdiamond R i j hne hji
  have hjd : fj D = D :=
    adjointWeyl_b2_fixes_double_bracket_rat P b hdiamond R i j hne hij
  obtain ⟨_, _, _, hCD, _, _, _, _, _, _, _⟩ :=
    raisingOver_g2_cross_brackets P b hdiamond R i j hne hij hji
  change C * D - D * C = -F at hCD
  have hjl : fj L = F := by
    calc
      fj L = -(C * D - D * C) := by
        change fj (A * D - D * A) = _
        rw [map_sub, map_mul, map_mul, hjd]
        change (nj.val * A * (nj⁻¹).val) * D -
          D * (nj.val * A * (nj⁻¹).val) = _
        rw [hja]
        simp only [neg_mul, mul_neg]
        abel
      _ = F := by rw [hCD, neg_neg]
  have hlong : fj (fi B) = (1 / 6 : ℚ) • F := by
    change fj (ni.val * B * (ni⁻¹).val) = _
    rw [hib]
    change nj.val * ((1 / 6 : ℚ) • L) * (nj⁻¹).val = _
    rw [mul_smul_comm, smul_mul_assoc]
    exact congrArg (fun X => (1 / 6 : ℚ) • X) hjl
  refine ⟨hja, ?_, hib, ?_⟩
  · change ni.val * (nj.val * A * (nj⁻¹).val) * (ni⁻¹).val = _ at hshort
    simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using hshort
  · change nj.val * (ni.val * B * (ni⁻¹).val) * (nj⁻¹).val = _ at hlong
    simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using hlong

/-- The four normalized composite operators are genuinely nilpotent,
because each is an actual Weyl conjugate of a simple raising operator. -/
theorem raisingOver_g2_positive_brackets_nilpotent
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let A := raisingOver P b R i
    let B := raisingOver P b R j
    let C := A * B - B * A
    let D := A * C - C * A
    let L := A * D - D * A
    let F := B * L - L * B
    IsNilpotent C ∧ IsNilpotent ((1 / 2 : ℚ) • D) ∧
      IsNilpotent ((1 / 6 : ℚ) • L) ∧ IsNilpotent ((1 / 6 : ℚ) • F) := by
  obtain ⟨hC, hD, hL, hF⟩ :=
    adjointWeyl_g2_positive_operator_pinnings P b hdiamond R i j hne hij hji
  have nil (u : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
      (k : b.support) :
      IsNilpotent (u.val * raisingOver P b R k * (u⁻¹).val) := by
    exact (raisingOver_nilpotent P b R k).map
      (MulSemiringAction.toRingHom
        (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
        (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct u))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := nil (adjointWeyl P b R j 1).val i
    rw [hC] at h
    simpa only [neg_neg] using h.neg
  · have h := nil ((adjointWeyl P b R i 1).val * (adjointWeyl P b R j 1).val) i
    rwa [hD] at h
  · have h := nil (adjointWeyl P b R i 1).val j
    rwa [hL] at h
  · have h := nil ((adjointWeyl P b R j 1).val * (adjointWeyl P b R i 1).val) j
    rwa [hF] at h

end Atlas.Chevalley
