import Atlas.LinearGroups.Chevalley.Integral.MinusculeDoubleEdge
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylTorus
import Atlas.Algebra.WeylOperatorPinning
import Atlas.Algebra.WeylOperatorPinningTwo

/-! Rational Weyl-pinning interfaces for the actual minuscule double edge.
The integral model remains the original transvection model. Division by two
is confined to this rational-algebra intermediate and is not used in finite
characteristic. Both signs act on the same original weight set. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

namespace Strings
variable {I Ω : Type*} (T : Strings I Ω)
  (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The actual square-zero transvection is its finite exponential over a
rational algebra; this requires no nilpotence hypothesis supplied by the caller. -/
theorem transvection_eq_nilpotent_exp (i : I) (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    T.transvection R i ε t = IsNilpotent.exp (t • T.step R i ε) := by
  have hz : (t • T.step R i ε) ^ 2 = 0 := by
    have hstep : T.step R i ε ^ 2 = 0 := by
      simpa only [pow_two] using T.step_square R i ε hε
    rw [smul_pow, hstep, smul_zero]
  rw [IsNilpotent.exp_eq_sum hz]
  simp [transvection, Finset.sum_range_succ]

/-- The exponential word is literally the already defined positive Weyl
operator, not a new representation or an assumed comparison map. -/
theorem weylEquiv_toLinearMap_eq_exp_word (i : I) :
    (T.weylEquiv R i 1).toLinearMap =
      IsNilpotent.exp (T.raising R i) * IsNilpotent.exp (-T.lowering R i) *
        IsNilpotent.exp (T.raising R i) := by
  change T.transvection R i (-1) 1 * T.transvection R i 1 (-1) *
    T.transvection R i (-1) 1 = _
  simp only [T.transvection_eq_nilpotent_exp R i (-1) (by decide) 1,
    T.transvection_eq_nilpotent_exp R i 1 (by decide) (-1),
    one_smul, raising, lowering]
  rw [neg_one_smul R (T.step R i 1)]

end Strings

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Algebra ℚ R]

/-- Rational positive pinning of the actual length-three double-edge string.
The only Cartan premise is row j, column i=-2. No raising operator is assumed nonzero. -/
theorem weightOrbit_doubleEdge_weyl_raising_exp (b : P.Base)
    (i j : b.support) (hne : i ≠ j) (hji : P.pairingIn ℤ j.val i.val = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    let A := T.raising R i.val
    let F := T.lowering R i.val
    let B := T.raising R j.val
    let C := A * B - B * A
    let D := A * C - C * A
    IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A * B *
        IsNilpotent.exp (-A) * IsNilpotent.exp F * IsNilpotent.exp (-A) =
      (1 / 2 : ℚ) • D := by
  let T := stringsOfWeightOrbit P S hc hm
  let A := T.raising R i.val
  let F := T.lowering R i.val
  let B := T.raising R j.val
  let C := A * B - B * A
  let D := A * C - C * A
  have hA : IsNilpotent A := ⟨2, by simpa only [pow_two] using T.raising_square R i.val⟩
  have hF : IsNilpotent F := ⟨2, by simpa only [pow_two] using T.lowering_square R i.val⟩
  have hAD : Commute A D := by
    have h := weightOrbit_step_cubic_serre P S hc hm R i.val j.val (-1) (by decide)
    change A * D - D * A = 0 at h
    exact sub_eq_zero.mp h
  have hFB : Commute F B :=
    (weightOrbit_opposite_steps_commute P S hc hm b j i hne.symm R).symm
  have hFC : F * C - C * F = (2 : ℚ) • B := by
    have h := weightOrbit_lowering_raising_bracket P S hc hm R b i j hne
    change F * C - C * F = (-P.pairingIn ℤ j.val i.val) • B at h
    simpa only [hji, neg_neg, two_smul] using h
  have hFD : F * D - D * F = (2 : ℚ) • C := by
    have h := weightOrbit_doubleEdge_lowering_double_bracket P S hc hm R b i j hne hji
    change F * D - D * F = (2 : ℤ) • C at h
    simpa only [two_smul] using h
  exact Atlas.Algebra.weyl_word_conjugate_operator_eq_half A F B C D
    hA hF rfl rfl hAD hFB hFC hFD

/-- Negative pinning uses F_i,E_i,F_j on the original orbit. It does not
negate the weights or assume that a selected minuscule orbit is negation-closed. -/
theorem weightOrbit_doubleEdge_weyl_lowering_exp (b : P.Base)
    (i j : b.support) (hne : i ≠ j) (hji : P.pairingIn ℤ j.val i.val = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    let A := T.lowering R i.val
    let F := T.raising R i.val
    let B := T.lowering R j.val
    let C := A * B - B * A
    let D := A * C - C * A
    IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A * B *
        IsNilpotent.exp (-A) * IsNilpotent.exp F * IsNilpotent.exp (-A) =
      (1 / 2 : ℚ) • D := by
  let T := stringsOfWeightOrbit P S hc hm
  let A := T.lowering R i.val
  let F := T.raising R i.val
  let B := T.lowering R j.val
  let C := A * B - B * A
  let D := A * C - C * A
  have hA : IsNilpotent A := ⟨2, by simpa only [pow_two] using T.lowering_square R i.val⟩
  have hF : IsNilpotent F := ⟨2, by simpa only [pow_two] using T.raising_square R i.val⟩
  have hAD : Commute A D := by
    have h := weightOrbit_step_cubic_serre P S hc hm R i.val j.val 1 (by decide)
    change A * D - D * A = 0 at h
    exact sub_eq_zero.mp h
  have hFB : Commute F B :=
    weightOrbit_opposite_steps_commute P S hc hm b i j hne R
  have hFC : F * C - C * F = (2 : ℚ) • B := by
    have h := weightOrbit_raising_lowering_bracket P S hc hm R b i j hne
    change F * C - C * F = (-P.pairingIn ℤ j.val i.val) • B at h
    simpa only [hji, neg_neg, two_smul] using h
  have hFD : F * D - D * F = (2 : ℚ) • C := by
    have h := weightOrbit_doubleEdge_raising_double_bracket P S hc hm R b i j hne hji
    change F * D - D * F = (2 : ℤ) • C at h
    simpa only [two_smul] using h
  exact Atlas.Algebra.weyl_word_conjugate_operator_eq_half A F B C D
    hA hF rfl rfl hAD hFB hFC hFD

/-- The reverse Cartan -1 direction needs only that one entry, so this
pinning applies to a double edge as well as a simply laced edge. -/
theorem weightOrbit_singleEdge_weyl_raising_exp (b : P.Base)
    (i j : b.support) (hne : i ≠ j) (hji : P.pairingIn ℤ j.val i.val = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    let A := T.raising R i.val
    let F := T.lowering R i.val
    let B := T.raising R j.val
    let C := A * B - B * A
    IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A * B *
        IsNilpotent.exp (-A) * IsNilpotent.exp F * IsNilpotent.exp (-A) = C := by
  let T := stringsOfWeightOrbit P S hc hm
  let A := T.raising R i.val
  let F := T.lowering R i.val
  let B := T.raising R j.val
  let C := A * B - B * A
  have hA : IsNilpotent A := ⟨2, by simpa only [pow_two] using T.raising_square R i.val⟩
  have hF : IsNilpotent F := ⟨2, by simpa only [pow_two] using T.lowering_square R i.val⟩
  have hAC : Commute A C := by
    have h := weightOrbit_doubleEdge_reverse_serre P S hc hm R j.val i.val hji (-1) (by decide)
    change A * C - C * A = 0 at h
    exact sub_eq_zero.mp h
  have hFB : Commute F B :=
    (weightOrbit_opposite_steps_commute P S hc hm b j i hne.symm R).symm
  have hFC : F * C - C * F = B := by
    have h := weightOrbit_lowering_raising_bracket P S hc hm R b i j hne
    change F * C - C * F = (-P.pairingIn ℤ j.val i.val) • B at h
    simpa only [hji, neg_neg, one_smul] using h
  exact Atlas.Algebra.weyl_word_conjugate_operator_eq A F B C hA hF rfl hAC hFB hFC

/-- The reverse -1 pinning with all root signs reversed on the same orbit. -/
theorem weightOrbit_singleEdge_weyl_lowering_exp (b : P.Base)
    (i j : b.support) (hne : i ≠ j) (hji : P.pairingIn ℤ j.val i.val = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    let A := T.lowering R i.val
    let F := T.raising R i.val
    let B := T.lowering R j.val
    let C := A * B - B * A
    IsNilpotent.exp A * IsNilpotent.exp (-F) * IsNilpotent.exp A * B *
        IsNilpotent.exp (-A) * IsNilpotent.exp F * IsNilpotent.exp (-A) = C := by
  let T := stringsOfWeightOrbit P S hc hm
  let A := T.lowering R i.val
  let F := T.raising R i.val
  let B := T.lowering R j.val
  let C := A * B - B * A
  have hA : IsNilpotent A := ⟨2, by simpa only [pow_two] using T.lowering_square R i.val⟩
  have hF : IsNilpotent F := ⟨2, by simpa only [pow_two] using T.raising_square R i.val⟩
  have hAC : Commute A C := by
    have h := weightOrbit_doubleEdge_reverse_serre P S hc hm R j.val i.val hji 1 (by decide)
    change A * C - C * A = 0 at h
    exact sub_eq_zero.mp h
  have hFB : Commute F B :=
    weightOrbit_opposite_steps_commute P S hc hm b i j hne R
  have hFC : F * C - C * F = B := by
    have h := weightOrbit_raising_lowering_bracket P S hc hm R b i j hne
    change F * C - C * F = (-P.pairingIn ℤ j.val i.val) • B at h
    simpa only [hji, neg_neg, one_smul] using h
  exact Atlas.Algebra.weyl_word_conjugate_operator_eq A F B C hA hF rfl hAC hFB hFC

end Atlas.Chevalley.Integral.Minuscule
