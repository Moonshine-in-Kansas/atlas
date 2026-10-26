import Atlas.Algebra.SquareZeroCommutator
import Atlas.LinearGroups.Chevalley.Integral.MinusculeOpposite
import Mathlib.Algebra.Group.Commutator

/-! Integral A2 triple-product vanishing and root commutators on actual
reflection-closed minuscule weight sets. Both raising and lowering signs are
covered without any closure under weight negation. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- On a single Cartan edge, three alternating equal-sign steps vanish.
Only the indicated Cartan entry is needed for this orientation. -/
theorem weightOrbit_step_sandwich_eq_zero (i j : ι)
    (hji : P.pairingIn ℤ j i = -1) (ε : ℤ) (hε : ε ≠ 0) :
    (stringsOfWeightOrbit P S hc hm).step R i ε *
      (stringsOfWeightOrbit P S hc hm).step R j ε *
        (stringsOfWeightOrbit P S hc hm).step R i ε = 0 := by
  let T := stringsOfWeightOrbit P S hc hm
  have grade (ν : WeightOrbit P S) :
      T.pairing i (T.reflection j ν) =
        T.pairing i ν - T.pairing j ν * P.pairingIn ℤ j i :=
    weightReflection_other_grade P i j ν.val
  apply Finsupp.lhom_ext
  intro μ r
  change T.step R i ε (T.step R j ε (T.step R i ε (Finsupp.single μ r))) = 0
  by_cases hi : T.pairing i μ = ε
  · by_cases hj : T.pairing j (T.reflection i μ) = ε
    · have hfinal : T.pairing i (T.reflection j (T.reflection i μ)) = 0 := by
        rw [grade, T.pairing_reflection, hi, hj, hji]
        ring
      have hfinal_ne : T.pairing i (T.reflection j (T.reflection i μ)) ≠ ε := by
        rw [hfinal]
        exact Ne.symm hε
      simp [Strings.step_single, hi, hj, hfinal_ne]
    · simp [hi, hj]
  · simp [hi]

theorem weightOrbit_raising_a2_sandwiches (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    T.raising R i * T.raising R j * T.raising R i = 0 ∧
      T.raising R j * T.raising R i * T.raising R j = 0 := by
  exact ⟨weightOrbit_step_sandwich_eq_zero P S hc hm R i j hji (-1) (by decide),
    weightOrbit_step_sandwich_eq_zero P S hc hm R j i hij (-1) (by decide)⟩

theorem weightOrbit_lowering_a2_sandwiches (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    T.lowering R i * T.lowering R j * T.lowering R i = 0 ∧
      T.lowering R j * T.lowering R i * T.lowering R j = 0 := by
  exact ⟨weightOrbit_step_sandwich_eq_zero P S hc hm R i j hji 1 (by decide),
    weightOrbit_step_sandwich_eq_zero P S hc hm R j i hij 1 (by decide)⟩

theorem weightOrbit_stepMatrix_sandwich_eq_zero (i j : ι)
    (hji : P.pairingIn ℤ j i = -1) (ε : ℤ) (hε : ε ≠ 0) :
    (stringsOfWeightOrbit P S hc hm).stepMatrix R i ε *
      (stringsOfWeightOrbit P S hc hm).stepMatrix R j ε *
        (stringsOfWeightOrbit P S hc hm).stepMatrix R i ε = 0 := by
  have h := congrArg (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne)
    (weightOrbit_step_sandwich_eq_zero P S hc hm R i j hji ε hε)
  simpa only [LinearMap.toMatrix_mul, map_zero, Strings.stepMatrix] using h

/-- Literal four-factor operator word; no abstract root-group relation is assumed. -/
theorem weightOrbit_transvection_a2_commutator_expansion (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1)
    (ε : ℤ) (hε : ε ≠ 0) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.transvection R i ε s * T.transvection R j ε t *
        T.transvection R i ε (-s) * T.transvection R j ε (-t) =
      1 + (s * t) • (T.step R i ε * T.step R j ε - T.step R j ε * T.step R i ε) := by
  exact Atlas.Algebra.squareZero_scaled_commutator_expansion
    ((stringsOfWeightOrbit P S hc hm).step R i ε)
    ((stringsOfWeightOrbit P S hc hm).step R j ε)
    ((stringsOfWeightOrbit P S hc hm).step_square R i ε hε)
    ((stringsOfWeightOrbit P S hc hm).step_square R j ε hε)
    (weightOrbit_step_sandwich_eq_zero P S hc hm R i j hji ε hε)
    (weightOrbit_step_sandwich_eq_zero P S hc hm R j i hij ε hε) s t

theorem weightOrbit_rootMatrix_a2_commutator_expansion (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1)
    (ε : ℤ) (hε : ε ≠ 0) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.rootMatrix R i ε s * T.rootMatrix R j ε t *
        T.rootMatrix R i ε (-s) * T.rootMatrix R j ε (-t) =
      1 + (s * t) • (T.stepMatrix R i ε * T.stepMatrix R j ε -
        T.stepMatrix R j ε * T.stepMatrix R i ε) := by
  exact Atlas.Algebra.squareZero_scaled_commutator_expansion
    ((stringsOfWeightOrbit P S hc hm).stepMatrix R i ε)
    ((stringsOfWeightOrbit P S hc hm).stepMatrix R j ε)
    ((stringsOfWeightOrbit P S hc hm).stepMatrix_square R i ε hε)
    ((stringsOfWeightOrbit P S hc hm).stepMatrix_square R j ε hε)
    (weightOrbit_stepMatrix_sandwich_eq_zero P S hc hm R i j hji ε hε)
    (weightOrbit_stepMatrix_sandwich_eq_zero P S hc hm R j i hij ε hε) s t

/-- The commutator of the actual matrix units, for either equal sign.
Its displayed value uses only the actual integral weight-step matrices. -/
theorem weightOrbit_rootElements_a2_commutator_val (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1)
    (ε : ℤ) (hε : ε ≠ 0) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    (⁅weightOrbitRootElement P S hc hm R i ε hε s,
      weightOrbitRootElement P S hc hm R j ε hε t⁆).val =
        1 + (s * t) • (T.stepMatrix R i ε * T.stepMatrix R j ε -
          T.stepMatrix R j ε * T.stepMatrix R i ε) := by
  change (stringsOfWeightOrbit P S hc hm).rootMatrix R i ε s *
      (stringsOfWeightOrbit P S hc hm).rootMatrix R j ε t *
      (stringsOfWeightOrbit P S hc hm).rootMatrix R i ε (-s) *
      (stringsOfWeightOrbit P S hc hm).rootMatrix R j ε (-t) = _
  exact weightOrbit_rootMatrix_a2_commutator_expansion P S hc hm R i j hij hji ε hε s t

end Atlas.Chevalley.Integral.Minuscule
