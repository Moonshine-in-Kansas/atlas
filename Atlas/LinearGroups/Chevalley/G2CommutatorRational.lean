import Atlas.Algebra.TripleEdgeExponential
import Atlas.LinearAlgebra.HeightDepthNilpotent
import Atlas.LinearGroups.Chevalley.G2PositiveOperatorPinning
import Atlas.LinearGroups.Chevalley.Integral.HeightTriangular

/-! Source candidate: the actual four-factor rational G2 commutator, with
all positive sum-nilpotence supplied by the concrete adjoint height. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]

private theorem raisingOver_heightAtLeast_one (i : b.support) :
    Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 (raisingOver P b R i) := by
  intro row col h
  have hz : raising P b i row col = 0 := by
    by_contra hn
    have hs := raising_height_weightedSupport P b i row col hn
    omega
  simp only [raisingOver, Matrix.map_apply, hz, map_zero]

private theorem heightAtLeast_bracket
    {A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hA : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 A)
    (hB : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 B) :
    Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 (A * B - B * A) :=
  ((hA.mul hB).mono (by decide)).sub ((hB.mul hA).mono (by decide))

private theorem adjoint_unit_conjugate_raisingExponential
    (u : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
    (k : b.support) (t : R) :
    u.val * raisingExponential P b R k t * (u⁻¹).val =
      IsNilpotent.exp (t • (u.val * raisingOver P b R k * (u⁻¹).val)) := by
  have h := IsNilpotent.exp_smul (ConjAct.toConjAct u)
    ((raisingOver_nilpotent P b R k).smul t)
  change IsNilpotent.exp (u.val * (t • raisingOver P b R k) * (u⁻¹).val) =
    u.val * IsNilpotent.exp (t • raisingOver P b R k) * (u⁻¹).val at h
  rw [mul_smul_comm, smul_mul_assoc,
    ← raisingExponential_eq_nilpotent_exp P b R k t] at h
  exact h.symm

include hdiamond

/-- For i short and j long, the literal increasing-height G2 factors have
parameters -st, s²t, s³t, 2s³t² and Weyl words j, ij, i, ji. Only this
intermediate theorem assumes a rational algebra; integral descent is separate. -/
theorem adjointX_g2_commutator_eq_weyl_product_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    ⁅adjointX P b R i s, adjointX P b R j t⁆ =
      (adjointWeyl P b R j 1 * adjointX P b R i (-s*t) *
        (adjointWeyl P b R j 1)⁻¹) *
      ((adjointWeyl P b R i 1 * adjointWeyl P b R j 1) *
        adjointX P b R i (s^2*t) * (adjointWeyl P b R i 1 * adjointWeyl P b R j 1)⁻¹) *
      (adjointWeyl P b R i 1 * adjointX P b R j (s^3*t) *
        (adjointWeyl P b R i 1)⁻¹) *
      ((adjointWeyl P b R j 1 * adjointWeyl P b R i 1) *
        adjointX P b R j (2*s^3*t^2) *
          (adjointWeyl P b R j 1 * adjointWeyl P b R i 1)⁻¹) := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  let F := B * L - L * B
  let ni := (adjointWeyl P b R i 1).val
  let nj := (adjointWeyl P b R j 1).val
  obtain ⟨hAL, hBC, hBD, hCD, hCL, hDL, _, hBF, hCF, hDF, hLF⟩ :=
    raisingOver_g2_cross_brackets P b hdiamond R i j hne hij hji
  have ha : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 A :=
    raisingOver_heightAtLeast_one P b R i
  have hb : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 B :=
    raisingOver_heightAtLeast_one P b R j
  have hc : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 C :=
    heightAtLeast_bracket P b R ha hb
  have hd : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 D :=
    heightAtLeast_bracket P b R ha hc
  have hl : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 L :=
    heightAtLeast_bracket P b R ha hd
  have hf : Atlas.Matrix.HeightAtLeast (geckHeight P b) 1 F :=
    heightAtLeast_bracket P b R hb hl
  have scaledBracket (a c : R)
      (U V : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
      (a • U) * (c • V) - (c • V) * (a • U) = (a*c) • (U*V-V*U) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm c a, smul_sub]
  have hABs : (s • A) * (t • B) - (t • B) * (s • A) = (s*t) • C :=
    scaledBracket s t A B
  have hACs : (s • A) * ((s*t) • C) - ((s*t) • C) * (s • A) = (s^2*t) • D := by
    rw [scaledBracket]
    congr 1
    ring
  have hADs : (s • A) * ((s^2*t) • D) - ((s^2*t) • D) * (s • A) = (s^3*t) • L := by
    rw [scaledBracket]
    congr 1
    ring
  have hBLs : (t • B) * ((s^3*t) • L) - ((s^3*t) • L) * (t • B) =
      (s^3*t^2) • F := by
    rw [scaledBracket]
    congr 1
    ring
  have hCDs : ((s*t) • C) * ((s^2*t) • D) - ((s^2*t) • D) * ((s*t) • C) =
      -((s^3*t^2) • F) := by
    change C * D - D * C = -F at hCD
    rw [scaledBracket, hCD, smul_neg]
    congr 2
    ring
  have hsum : IsNilpotent ((s*t) • C + (1 / 2 : ℚ) • ((s^2*t) • D)) :=
    ((hc.smul (s*t)).add ((hd.smul (s^2*t)).smul (1 / 2 : ℚ))).isNilpotent_of_pos (by decide)
  have hcalc := Atlas.Algebra.exp_tripleEdge_commutator
    (s • A) (t • B) ((s*t) • C) ((s^2*t) • D) ((s^3*t) • L) ((s^3*t^2) • F)
    ((ha.smul s).isNilpotent_of_pos (by decide))
    ((hb.smul t).isNilpotent_of_pos (by decide))
    ((hc.smul (s*t)).isNilpotent_of_pos (by decide))
    ((hd.smul (s^2*t)).isNilpotent_of_pos (by decide))
    ((hl.smul (s^3*t)).isNilpotent_of_pos (by decide))
    ((hf.smul (s^3*t^2)).isNilpotent_of_pos (by decide)) hsum
    hABs hACs hADs ((hAL.smul_left s).smul_right (s^3*t))
    ((hBC.smul_left t).smul_right (s*t))
    ((hBD.smul_left t).smul_right (s^2*t)) hBLs hCDs
    ((hCL.smul_left (s*t)).smul_right (s^3*t))
    ((hDL.smul_left (s^2*t)).smul_right (s^3*t))
    ((hBF.smul_left t).smul_right (s^3*t^2))
    ((hCF.smul_left (s*t)).smul_right (s^3*t^2))
    ((hDF.smul_left (s^2*t)).smul_right (s^3*t^2))
    ((hLF.smul_left (s^3*t)).smul_right (s^3*t^2))
  obtain ⟨hpinC, hpinD, hpinL, hpinF⟩ :=
    adjointWeyl_g2_positive_operator_pinnings P b hdiamond R i j hne hij hji
  have hZ : nj.val * raisingExponential P b R i (-s*t) * (nj⁻¹).val =
      IsNilpotent.exp ((s*t) • C) := by
    rw [adjoint_unit_conjugate_raisingExponential P b R, hpinC]
    simp only [neg_mul, neg_smul, smul_neg, neg_neg, A, B, C]
  have hW : (ni * nj).val * raisingExponential P b R i (s^2*t) * ((ni * nj)⁻¹).val =
      IsNilpotent.exp ((1 / 2 : ℚ) • ((s^2*t) • D)) := by
    rw [adjoint_unit_conjugate_raisingExponential P b R, hpinD]
    congr 1
    exact smul_comm (s^2*t) (1 / 2 : ℚ) D
  have hV : ni.val * raisingExponential P b R j (s^3*t) * (ni⁻¹).val =
      IsNilpotent.exp ((1 / 6 : ℚ) • ((s^3*t) • L)) := by
    rw [adjoint_unit_conjugate_raisingExponential P b R, hpinL]
    congr 1
    exact smul_comm (s^3*t) (1 / 6 : ℚ) L
  have hH : (nj * ni).val * raisingExponential P b R j (2*s^3*t^2) * ((nj * ni)⁻¹).val =
      IsNilpotent.exp ((1 / 3 : ℚ) • ((s^3*t^2) • F)) := by
    rw [adjoint_unit_conjugate_raisingExponential P b R, hpinF]
    change IsNilpotent.exp ((2*s^3*t^2) • ((1 / 6 : ℚ) • F)) = _
    congr 1
    have htwice : 2*s^3*t^2 = (s^3*t^2) + (s^3*t^2) := by ring
    rw [htwice, add_smul, ← smul_add, ← add_smul,
      show (1 / 6 : ℚ) + 1 / 6 = 1 / 3 by norm_num]
    exact smul_comm (s^3*t^2) (1 / 3 : ℚ) F
  apply Subtype.ext
  apply Units.ext
  change raisingExponential P b R i s * raisingExponential P b R j t *
      raisingExponential P b R i (-s) * raisingExponential P b R j (-t) =
    (nj.val * raisingExponential P b R i (-s*t) * (nj⁻¹).val) *
      ((ni * nj).val * raisingExponential P b R i (s^2*t) * ((ni * nj)⁻¹).val) *
      (ni.val * raisingExponential P b R j (s^3*t) * (ni⁻¹).val) *
      ((nj * ni).val * raisingExponential P b R j (2*s^3*t^2) * ((nj * ni)⁻¹).val)
  rw [hZ, hW, hV, hH]
  simpa only [A, B, raisingExponential_eq_nilpotent_exp, neg_smul] using hcalc

end Atlas.Chevalley
