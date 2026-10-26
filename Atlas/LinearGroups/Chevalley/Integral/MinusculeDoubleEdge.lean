import Atlas.LinearGroups.Chevalley.Integral.MinusculeA2Commutator
import Atlas.LinearGroups.Chevalley.Integral.MinusculeCartanOperators
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Module

/-! Local double-edge identities on the actual integral minuscule weight set.
The root operators may vanish; neither nonzero primitive vectors nor closure
under weight negation is assumed. Every identity holds over any commutative ring. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem squareZero_cubic_serre {A : Type*} [Ring A]
    (e b : A) (hee : e * e = 0) :
    e * (e * (e * b - b * e) - (e * b - b * e) * e) -
      (e * (e * b - b * e) - (e * b - b * e) * e) * e = 0 := by
  calc
    _ = (e * e) * (e * b) - (e * e) * (b * e) -
        (e * e) * (b * e) - (e * e) * (b * e) +
        (e * b) * (e * e) + (e * b) * (e * e) +
        (e * b) * (e * e) - (b * e) * (e * e) := by noncomm_ring
    _ = 0 := by simp only [hee, zero_mul, mul_zero, sub_zero, zero_add]

private theorem squareZero_sandwich_serre {A : Type*} [Ring A]
    (e b : A) (hee : e * e = 0) (heb : e * b * e = 0) :
    e * (e * b - b * e) - (e * b - b * e) * e = 0 := by
  calc
    _ = (e * e) * b + b * (e * e) - e * b * e - e * b * e := by noncomm_ring
    _ = 0 := by simp only [hee, heb, zero_mul, mul_zero, zero_add, sub_zero]

private theorem lowering_bracket_of_cartan {A : Type*} [Ring A]
    (e f h b : A) (c : ℤ)
    (hef : ⁅e, f⁆ = h) (hfb : ⁅f, b⁆ = 0) (hhb : ⁅h, b⁆ = c • b) :
    ⁅f, ⁅e, b⁆⁆ = (-c) • b := by
  have hfe : ⁅f, e⁆ = -h := by rw [← lie_skew, hef]
  rw [leibniz_lie, hfe, hfb, neg_lie, hhb, lie_zero, add_zero]
  module

private theorem lowering_double_bracket_of_cartan {A : Type*} [Ring A]
    (e f h b : A)
    (hef : ⁅e, f⁆ = h) (hfb : ⁅f, b⁆ = 0)
    (hhe : ⁅h, e⁆ = (2 : ℤ) • e) (hhb : ⁅h, b⁆ = (-2 : ℤ) • b) :
    ⁅f, ⁅e, ⁅e, b⁆⁆⁆ = (2 : ℤ) • ⁅e, b⁆ := by
  have hfe : ⁅f, e⁆ = -h := by rw [← lie_skew, hef]
  have hfc : ⁅f, ⁅e, b⁆⁆ = (2 : ℤ) • b := by
    simpa only [neg_neg] using lowering_bracket_of_cartan e f h b (-2) hef hfb hhb
  have hhc : ⁅h, ⁅e, b⁆⁆ = 0 := by
    rw [leibniz_lie, hhe, hhb, smul_lie, lie_smul]
    module
  rw [leibniz_lie, hfe, hfc, neg_lie, hhc, neg_zero, zero_add, lie_smul]

-- Present the already proved Lie calculation through literal associative
-- expressions before specializing to Module.End, whose Lie structures need
-- not reduce through the same instance path during elaboration.
private theorem lowering_bracket_of_cartan_assoc {A : Type*} [Ring A]
    (e f h b : A) (c : ℤ)
    (hef : e * f - f * e = h) (hfb : f * b - b * f = 0)
    (hhb : h * b - b * h = c • b) :
    f * (e * b - b * e) - (e * b - b * e) * f = (-c) • b := by
  exact lowering_bracket_of_cartan e f h b c hef hfb hhb

private theorem lowering_double_bracket_of_cartan_assoc {A : Type*} [Ring A]
    (e f h b : A)
    (hef : e * f - f * e = h) (hfb : f * b - b * f = 0)
    (hhe : h * e - e * h = (2 : ℤ) • e)
    (hhb : h * b - b * h = (-2 : ℤ) • b) :
    f * (e * (e * b - b * e) - (e * b - b * e) * e) -
      (e * (e * b - b * e) - (e * b - b * e) * e) * f =
        (2 : ℤ) • (e * b - b * e) := by
  exact lowering_double_bracket_of_cartan e f h b hef hfb hhe hhb

private theorem negate_left_commutator {A : Type*} [Ring A] (a b : A) :
    (-a) * b - b * (-a) = -(a * b - b * a) := by
  noncomm_ring

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

private theorem grade_raising_sub_int (i j : ι) :
    let T := stringsOfWeightOrbit P S hc hm
    T.gradeOperator R j * T.raising R i - T.raising R i * T.gradeOperator R j =
      P.pairingIn ℤ i j • T.raising R i := by
  let T := stringsOfWeightOrbit P S hc hm
  have h := weightOrbit_grade_raising_sub P S hc hm R i j
  change T.gradeOperator R j * T.raising R i - T.raising R i * T.gradeOperator R j =
    (P.pairingIn ℤ i j : R) • T.raising R i at h
  exact h.trans (Int.cast_smul_eq_zsmul R (P.pairingIn ℤ i j) (T.raising R i))

private theorem neg_grade_lowering_sub_int (i j : ι) :
    let T := stringsOfWeightOrbit P S hc hm
    (-T.gradeOperator R j) * T.lowering R i - T.lowering R i * (-T.gradeOperator R j) =
      P.pairingIn ℤ i j • T.lowering R i := by
  let T := stringsOfWeightOrbit P S hc hm
  have h := weightOrbit_grade_lowering_sub P S hc hm R i j
  change T.gradeOperator R j * T.lowering R i - T.lowering R i * T.gradeOperator R j =
    (-(P.pairingIn ℤ i j : R)) • T.lowering R i at h
  calc
    (-T.gradeOperator R j) * T.lowering R i - T.lowering R i * (-T.gradeOperator R j) =
        -(T.gradeOperator R j * T.lowering R i - T.lowering R i * T.gradeOperator R j) := by
      exact negate_left_commutator (T.gradeOperator R j) (T.lowering R i)
    _ = -((-(P.pairingIn ℤ i j : R)) • T.lowering R i) := congrArg Neg.neg h
    _ = (P.pairingIn ℤ i j : R) • T.lowering R i := by
      exact (congrArg Neg.neg (neg_smul (P.pairingIn ℤ i j : R) (T.lowering R i))).trans (neg_neg ((P.pairingIn ℤ i j : R) • T.lowering R i))
    _ = P.pairingIn ℤ i j • T.lowering R i :=
      Int.cast_smul_eq_zsmul R (P.pairingIn ℤ i j) (T.lowering R i)

/-- Cubic Serre follows from the actual square-zero step alone. It therefore
holds for both signs, without any edge or nonvanishing hypothesis. -/
theorem weightOrbit_step_cubic_serre (i j : ι) (ε : ℤ) (hε : ε ≠ 0) :
    let T := stringsOfWeightOrbit P S hc hm
    T.step R i ε * (T.step R i ε *
        (T.step R i ε * T.step R j ε - T.step R j ε * T.step R i ε) -
      (T.step R i ε * T.step R j ε - T.step R j ε * T.step R i ε) * T.step R i ε) -
      (T.step R i ε *
          (T.step R i ε * T.step R j ε - T.step R j ε * T.step R i ε) -
        (T.step R i ε * T.step R j ε - T.step R j ε * T.step R i ε) * T.step R i ε) *
          T.step R i ε = 0 := by
  exact squareZero_cubic_serre
    ((stringsOfWeightOrbit P S hc hm).step R i ε)
    ((stringsOfWeightOrbit P S hc hm).step R j ε)
    ((stringsOfWeightOrbit P S hc hm).step_square R i ε hε)

/-- The Cartan entry row i, column j=-1 kills the reverse sandwich.
This is the reverse direction of a double edge; the other entry is unneeded. -/
theorem weightOrbit_doubleEdge_reverse_sandwich (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (ε : ℤ) (hε : ε ≠ 0) :
    let T := stringsOfWeightOrbit P S hc hm
    T.step R j ε * T.step R i ε * T.step R j ε = 0 := by
  exact weightOrbit_step_sandwich_eq_zero P S hc hm R j i hij ε hε

/-- The reverse quadratic Serre relation, uniformly for the two signs. -/
theorem weightOrbit_doubleEdge_reverse_serre (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (ε : ℤ) (hε : ε ≠ 0) :
    let T := stringsOfWeightOrbit P S hc hm
    T.step R j ε * (T.step R j ε * T.step R i ε - T.step R i ε * T.step R j ε) -
      (T.step R j ε * T.step R i ε - T.step R i ε * T.step R j ε) * T.step R j ε = 0 := by
  exact squareZero_sandwich_serre
    ((stringsOfWeightOrbit P S hc hm).step R j ε)
    ((stringsOfWeightOrbit P S hc hm).step R i ε)
    ((stringsOfWeightOrbit P S hc hm).step_square R j ε hε)
    (weightOrbit_doubleEdge_reverse_sandwich P S hc hm R i j hij ε hε)

/-- The first lowering coefficient is the negative actual Cartan entry.
For a double edge this is 2; in the reverse direction it is 1. -/
theorem weightOrbit_lowering_raising_bracket (b : P.Base)
    (i j : b.support) (hne : i ≠ j) :
    let T := stringsOfWeightOrbit P S hc hm
    T.lowering R i.val * (T.raising R i.val * T.raising R j.val -
        T.raising R j.val * T.raising R i.val) -
      (T.raising R i.val * T.raising R j.val -
        T.raising R j.val * T.raising R i.val) * T.lowering R i.val =
      (-P.pairingIn ℤ j.val i.val) • T.raising R j.val := by
  let T := stringsOfWeightOrbit P S hc hm
  apply lowering_bracket_of_cartan_assoc (T.raising R i.val) (T.lowering R i.val)
    (T.gradeOperator R i.val) (T.raising R j.val) (P.pairingIn ℤ j.val i.val)
  · exact T.raising_lowering_sub R i.val
  · exact sub_eq_zero.mpr
      (weightOrbit_opposite_steps_commute P S hc hm b j i hne.symm R).symm.eq
  · exact grade_raising_sub_int P S hc hm R j.val i.val

/-- The same Cartan coefficient on the original weight set with the signs
reversed. No weight-negation operation or closure assumption occurs. -/
theorem weightOrbit_raising_lowering_bracket (b : P.Base)
    (i j : b.support) (hne : i ≠ j) :
    let T := stringsOfWeightOrbit P S hc hm
    T.raising R i.val * (T.lowering R i.val * T.lowering R j.val -
        T.lowering R j.val * T.lowering R i.val) -
      (T.lowering R i.val * T.lowering R j.val -
        T.lowering R j.val * T.lowering R i.val) * T.raising R i.val =
      (-P.pairingIn ℤ j.val i.val) • T.lowering R j.val := by
  let T := stringsOfWeightOrbit P S hc hm
  apply lowering_bracket_of_cartan_assoc (T.lowering R i.val) (T.raising R i.val)
    (-T.gradeOperator R i.val) (T.lowering R j.val) (P.pairingIn ℤ j.val i.val)
  · calc
      T.lowering R i.val * T.raising R i.val - T.raising R i.val * T.lowering R i.val =
          -(T.raising R i.val * T.lowering R i.val - T.lowering R i.val * T.raising R i.val) := by
        exact (neg_sub (T.raising R i.val * T.lowering R i.val)
          (T.lowering R i.val * T.raising R i.val)).symm
      _ = -T.gradeOperator R i.val := congrArg Neg.neg (T.raising_lowering_sub R i.val)
  · exact sub_eq_zero.mpr
      (weightOrbit_opposite_steps_commute P S hc hm b i j hne R).eq
  · exact neg_grade_lowering_sub_int P S hc hm R j.val i.val

/-- Both steps in the actual length-three raising string have coefficient 2.
This second identity requires only Cartan row j, column i=-2. -/
theorem weightOrbit_doubleEdge_lowering_double_bracket (b : P.Base)
    (i j : b.support) (hne : i ≠ j) (hji : P.pairingIn ℤ j.val i.val = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    let A := T.raising R i.val
    let B := T.raising R j.val
    let C := A * B - B * A
    let D := A * C - C * A
    T.lowering R i.val * D - D * T.lowering R i.val = (2 : ℤ) • C := by
  let T := stringsOfWeightOrbit P S hc hm
  apply lowering_double_bracket_of_cartan_assoc (T.raising R i.val) (T.lowering R i.val)
    (T.gradeOperator R i.val) (T.raising R j.val)
  · exact T.raising_lowering_sub R i.val
  · exact sub_eq_zero.mpr
      (weightOrbit_opposite_steps_commute P S hc hm b j i hne.symm R).symm.eq
  · have hii : P.pairingIn ℤ i.val i.val = 2 := b.cartanMatrix_apply_same i
    have h := grade_raising_sub_int P S hc hm R i.val i.val
    change T.gradeOperator R i.val * T.raising R i.val -
      T.raising R i.val * T.gradeOperator R i.val = P.pairingIn ℤ i.val i.val • T.raising R i.val at h
    rwa [hii] at h
  · have h := grade_raising_sub_int P S hc hm R j.val i.val
    change T.gradeOperator R i.val * T.raising R j.val -
      T.raising R j.val * T.gradeOperator R i.val = P.pairingIn ℤ j.val i.val • T.raising R j.val at h
    rwa [hji] at h

/-- The negative-root length-three string on the same weights. -/
theorem weightOrbit_doubleEdge_raising_double_bracket (b : P.Base)
    (i j : b.support) (hne : i ≠ j) (hji : P.pairingIn ℤ j.val i.val = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    let A := T.lowering R i.val
    let B := T.lowering R j.val
    let C := A * B - B * A
    let D := A * C - C * A
    T.raising R i.val * D - D * T.raising R i.val = (2 : ℤ) • C := by
  let T := stringsOfWeightOrbit P S hc hm
  apply lowering_double_bracket_of_cartan_assoc (T.lowering R i.val) (T.raising R i.val)
    (-T.gradeOperator R i.val) (T.lowering R j.val)
  · calc
      T.lowering R i.val * T.raising R i.val - T.raising R i.val * T.lowering R i.val =
          -(T.raising R i.val * T.lowering R i.val - T.lowering R i.val * T.raising R i.val) := by
        exact (neg_sub (T.raising R i.val * T.lowering R i.val)
          (T.lowering R i.val * T.raising R i.val)).symm
      _ = -T.gradeOperator R i.val := congrArg Neg.neg (T.raising_lowering_sub R i.val)
  · exact sub_eq_zero.mpr
      (weightOrbit_opposite_steps_commute P S hc hm b i j hne R).eq
  · have hii : P.pairingIn ℤ i.val i.val = 2 := b.cartanMatrix_apply_same i
    have h := neg_grade_lowering_sub_int P S hc hm R i.val i.val
    change (-T.gradeOperator R i.val) * T.lowering R i.val -
      T.lowering R i.val * (-T.gradeOperator R i.val) = P.pairingIn ℤ i.val i.val • T.lowering R i.val at h
    rwa [hii] at h
  · have h := neg_grade_lowering_sub_int P S hc hm R j.val i.val
    change (-T.gradeOperator R i.val) * T.lowering R j.val -
      T.lowering R j.val * (-T.gradeOperator R i.val) = P.pairingIn ℤ j.val i.val • T.lowering R j.val at h
    rwa [hji] at h

end Atlas.Chevalley.Integral.Minuscule
