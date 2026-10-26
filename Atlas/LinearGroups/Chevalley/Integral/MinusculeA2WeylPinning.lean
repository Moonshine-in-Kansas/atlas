import Atlas.LinearGroups.Chevalley.Integral.MinusculeA2Commutator
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation

/-! Actual signed Weyl pinning of A2 commutators on integral minuscule weights.
The lowering argument reverses grades on the same set; it does not negate
weights or require the selected orbit to be closed under negation. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
open scoped commutatorElement

private theorem strings_a2_weyl_conjugate_raising
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + T.pairing j μ) :
    (T.weylEquiv R i 1).toLinearMap * T.raising R j *
        ((T.weylEquiv R i 1)⁻¹).toLinearMap =
      T.raising R i * T.raising R j - T.raising R j * T.raising R i := by
  apply Finsupp.lhom_ext
  intro μ r
  change T.weylEquiv R i 1 (T.raising R j
      ((T.weylEquiv R i 1)⁻¹ (Finsupp.single μ r))) =
    T.raising R i (T.raising R j (Finsupp.single μ r)) -
      T.raising R j (T.raising R i (Finsupp.single μ r))
  have hlast : T.pairing i (T.reflection j (T.reflection i μ)) = T.pairing j μ := by
    rw [hji, T.pairing_reflection, hij]
    omega
  rcases T.minuscule i μ with hi | hi | hi <;>
    rcases T.minuscule j μ with hj | hj | hj
  all_goals
    simp [Strings.raising, T.inverse_weyl_one_single, Strings.step_single,
      hi, hj, hij, hji, hlast, T.pairing_reflection, T.weylEquiv_single_neg,
      T.weylEquiv_single_pos, T.weylEquiv_single_zero]

private theorem strings_a2_rootEquiv_commutator
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + T.pairing j μ)
    (hiji : T.raising R i * T.raising R j * T.raising R i = 0)
    (hjij : T.raising R j * T.raising R i * T.raising R j = 0) (s t : R) :
    ⁅T.rootEquiv R i (-1) (by decide) s, T.rootEquiv R j (-1) (by decide) t⁆ =
      T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s * t) *
        (T.weylEquiv R i 1)⁻¹ := by
  apply LinearEquiv.toLinearMap_injective
  have hleft :
      (⁅T.rootEquiv R i (-1) (by decide) s,
        T.rootEquiv R j (-1) (by decide) t⁆).toLinearMap =
      1 + (s * t) • (T.raising R i * T.raising R j - T.raising R j * T.raising R i) := by
    change T.transvection R i (-1) s * T.transvection R j (-1) t *
        T.transvection R i (-1) (-s) * T.transvection R j (-1) (-t) = _
    exact Atlas.Algebra.squareZero_scaled_commutator_expansion
      (T.raising R i) (T.raising R j) (T.raising_square R i) (T.raising_square R j)
      hiji hjij s t
  have hpin := strings_a2_weyl_conjugate_raising T R i j hij hji
  have hinverse : (T.weylEquiv R i 1).toLinearMap *
      ((T.weylEquiv R i 1)⁻¹).toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    change T.weylEquiv R i 1 ((T.weylEquiv R i 1)⁻¹ v) = v
    exact (T.weylEquiv R i 1).apply_symm_apply v
  have hright :
      (T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s * t) *
        (T.weylEquiv R i 1)⁻¹).toLinearMap =
      1 + (s * t) • (T.raising R i * T.raising R j - T.raising R j * T.raising R i) := by
    change (T.weylEquiv R i 1).toLinearMap * (1 + (s * t) • T.raising R j) *
      ((T.weylEquiv R i 1)⁻¹).toLinearMap = _
    simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hinverse, hpin]
  exact hleft.trans hright.symm

/-- Auxiliary grade reversal on the original index set. No weight is moved. -/
private def reversedStrings {I Ω : Type*} (T : Strings I Ω) : Strings I Ω where
  pairing i μ := -T.pairing i μ
  reflection := T.reflection
  involutive := T.involutive
  pairing_reflection i μ := by
    change -T.pairing i (T.reflection i μ) = -(-T.pairing i μ)
    rw [T.pairing_reflection]
  minuscule i μ := by
    change -T.pairing i μ = -1 ∨ -T.pairing i μ = 0 ∨ -T.pairing i μ = 1
    rcases T.minuscule i μ with h | h | h <;> omega

private theorem reversedStrings_step {I Ω : Type*}
    (T : Strings I Ω) (R : Type*) [CommRing R] (i : I) (ε : ℤ) :
    (reversedStrings T).step R i ε = T.step R i (-ε) := by
  apply Finsupp.lhom_ext
  intro μ r
  simp only [Strings.step_single]
  change (if -T.pairing i μ = ε then Finsupp.single (T.reflection i μ) r else 0) =
    (if T.pairing i μ = -ε then Finsupp.single (T.reflection i μ) r else 0)
  have h : -T.pairing i μ = ε ↔ T.pairing i μ = -ε := by omega
  simp only [h]

private theorem reversedStrings_rootEquiv {I Ω : Type*}
    (T : Strings I Ω) (R : Type*) [CommRing R] (i : I)
    (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    (reversedStrings T).rootEquiv R i ε hε t =
      T.rootEquiv R i (-ε) (neg_ne_zero.mpr hε) t := by
  apply LinearEquiv.toLinearMap_injective
  change 1 + t • (reversedStrings T).step R i ε = 1 + t • T.step R i (-ε)
  rw [reversedStrings_step]

private theorem reversedStrings_a2_grade {I Ω : Type*}
    (T : Strings I Ω) (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ) :
    ∀ μ, (reversedStrings T).pairing j ((reversedStrings T).reflection i μ) =
      (reversedStrings T).pairing j μ + (reversedStrings T).pairing i μ := by
  intro μ
  change -T.pairing j (T.reflection i μ) = -T.pairing j μ + -T.pairing i μ
  rw [hij]
  omega

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

private theorem weightOrbit_a2_grade (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (μ : WeightOrbit P S) :
    (stringsOfWeightOrbit P S hc hm).pairing j
        ((stringsOfWeightOrbit P S hc hm).reflection i μ) =
      (stringsOfWeightOrbit P S hc hm).pairing j μ +
        (stringsOfWeightOrbit P S hc hm).pairing i μ := by
  change weightReflection P i μ.val (corootElement P j) =
    μ.val (corootElement P j) + μ.val (corootElement P i)
  simpa only [hij, mul_neg_one, sub_neg_eq_add] using
    weightReflection_other_grade P j i μ.val

/-- Signed Weyl pinning of the actual raising-operator bracket. -/
theorem weightOrbit_a2_weyl_conjugate_raising (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    (T.weylEquiv R i 1).toLinearMap * T.raising R j *
        ((T.weylEquiv R i 1)⁻¹).toLinearMap =
      T.raising R i * T.raising R j - T.raising R j * T.raising R i := by
  exact strings_a2_weyl_conjugate_raising (stringsOfWeightOrbit P S hc hm) R i j
    (weightOrbit_a2_grade P S hc hm i j hij) (weightOrbit_a2_grade P S hc hm j i hji)

theorem weightOrbit_a2_rootEquiv_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    ⁅T.rootEquiv R i (-1) (by decide) s, T.rootEquiv R j (-1) (by decide) t⁆ =
      T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s * t) *
        (T.weylEquiv R i 1)⁻¹ := by
  obtain ⟨hiji, hjij⟩ := weightOrbit_raising_a2_sandwiches P S hc hm R i j hij hji
  exact strings_a2_rootEquiv_commutator (stringsOfWeightOrbit P S hc hm) R i j
    (weightOrbit_a2_grade P S hc hm i j hij) (weightOrbit_a2_grade P S hc hm j i hji)
    hiji hjij s t

/-- The actual positive root-unit commutator, with the existing pinned Weyl word. -/
theorem weightOrbit_a2_rootElements_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) (s t : R) :
    let W := weightOrbitRootElement P S hc hm R i (-1) (by decide) 1 *
      weightOrbitRootElement P S hc hm R i 1 (by decide) (-1) *
        weightOrbitRootElement P S hc hm R i (-1) (by decide) 1
    ⁅weightOrbitRootElement P S hc hm R i (-1) (by decide) s,
        weightOrbitRootElement P S hc hm R j (-1) (by decide) t⁆ =
      W * weightOrbitRootElement P S hc hm R j (-1) (by decide) (s * t) * W⁻¹ := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_a2_rootEquiv_commutator P S hc hm R i j hij hji s t)
  simpa only [weightOrbitRootElement, map_commutatorElement, map_mul, map_inv,
    Strings.equivMatrixHom_root, Strings.equivMatrixHom_weyl, Strings.weylMatrixUnit,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h

/-- The lowering bracket is pinned by Y_i(1) X_i(-1) Y_i(1).
Grade reversal uses the same actual weight set, not a negated orbit. -/
theorem weightOrbit_a2_negative_weyl_conjugate_lowering (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    let V := T.rootEquiv R i 1 (by decide) 1 *
      T.rootEquiv R i (-1) (by decide) (-1) * T.rootEquiv R i 1 (by decide) 1
    V.toLinearMap * T.lowering R j * (V⁻¹).toLinearMap =
      T.lowering R i * T.lowering R j - T.lowering R j * T.lowering R i := by
  let T := stringsOfWeightOrbit P S hc hm
  have h := strings_a2_weyl_conjugate_raising (reversedStrings T) R i j
    (reversedStrings_a2_grade T i j (weightOrbit_a2_grade P S hc hm i j hij))
    (reversedStrings_a2_grade T j i (weightOrbit_a2_grade P S hc hm j i hji))
  simpa only [T, Strings.weylEquiv, reversedStrings_rootEquiv, Strings.raising,
    reversedStrings_step, neg_neg, Strings.lowering, Units.inv_eq_val_inv,
    inv_one, Units.val_one] using h

theorem weightOrbit_a2_lowering_rootEquiv_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    let V := T.rootEquiv R i 1 (by decide) 1 *
      T.rootEquiv R i (-1) (by decide) (-1) * T.rootEquiv R i 1 (by decide) 1
    ⁅T.rootEquiv R i 1 (by decide) s, T.rootEquiv R j 1 (by decide) t⁆ =
      V * T.rootEquiv R j 1 (by decide) (s * t) * V⁻¹ := by
  let T := stringsOfWeightOrbit P S hc hm
  obtain ⟨hiji, hjij⟩ := weightOrbit_lowering_a2_sandwiches P S hc hm R i j hij hji
  have hreviji : (reversedStrings T).raising R i * (reversedStrings T).raising R j *
      (reversedStrings T).raising R i = 0 := by
    simpa only [Strings.raising, reversedStrings_step, neg_neg, Strings.lowering] using hiji
  have hrevjij : (reversedStrings T).raising R j * (reversedStrings T).raising R i *
      (reversedStrings T).raising R j = 0 := by
    simpa only [Strings.raising, reversedStrings_step, neg_neg, Strings.lowering] using hjij
  have h := strings_a2_rootEquiv_commutator (reversedStrings T) R i j
    (reversedStrings_a2_grade T i j (weightOrbit_a2_grade P S hc hm i j hij))
    (reversedStrings_a2_grade T j i (weightOrbit_a2_grade P S hc hm j i hji))
    hreviji hrevjij s t
  simpa only [T, Strings.weylEquiv, reversedStrings_rootEquiv, neg_neg,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h

/-- The actual negative root-unit commutator, before any central-kernel theorem. -/
theorem weightOrbit_a2_lowering_rootElements_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) (s t : R) :
    let V := weightOrbitRootElement P S hc hm R i 1 (by decide) 1 *
      weightOrbitRootElement P S hc hm R i (-1) (by decide) (-1) *
        weightOrbitRootElement P S hc hm R i 1 (by decide) 1
    ⁅weightOrbitRootElement P S hc hm R i 1 (by decide) s,
        weightOrbitRootElement P S hc hm R j 1 (by decide) t⁆ =
      V * weightOrbitRootElement P S hc hm R j 1 (by decide) (s * t) * V⁻¹ := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_a2_lowering_rootEquiv_commutator P S hc hm R i j hij hji s t)
  simpa only [weightOrbitRootElement, map_commutatorElement, map_mul, map_inv,
    Strings.equivMatrixHom_root] using h

end Atlas.Chevalley.Integral.Minuscule
