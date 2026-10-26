import Atlas.Algebra.SquareZeroDoubleEdge
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDoubleEdge
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation

/-! Actual minuscule double-edge group words over every commutative ring.
The signed Weyl action and the root transvections use the same original weights.
All polynomial identities are integral, including characteristic two. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
open scoped commutatorElement

private theorem strings_doubleEdge_weyl_pins
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ) :
    ((T.weylEquiv R j 1).toLinearMap * T.raising R i *
        ((T.weylEquiv R j 1)⁻¹).toLinearMap =
      T.raising R j * T.raising R i - T.raising R i * T.raising R j) ∧
    ((T.weylEquiv R i 1).toLinearMap * T.raising R j *
        ((T.weylEquiv R i 1)⁻¹).toLinearMap =
      -(T.raising R i * T.raising R j * T.raising R i)) := by
  constructor
  · apply Finsupp.lhom_ext
    intro μ r
    change T.weylEquiv R j 1 (T.raising R i
        ((T.weylEquiv R j 1)⁻¹ (Finsupp.single μ r))) =
      T.raising R j (T.raising R i (Finsupp.single μ r)) -
        T.raising R i (T.raising R j (Finsupp.single μ r))
    have hlast : T.pairing j (T.reflection i (T.reflection j μ)) =
        T.pairing i μ + T.pairing j μ := by
      rw [hij, T.pairing_reflection, hji]
      omega
    have hbound := T.minuscule i (T.reflection j μ)
    rw [hji] at hbound
    rcases T.minuscule i μ with hi | hi | hi <;>
      rcases T.minuscule j μ with hj | hj | hj
    all_goals try omega
    all_goals
      simp [Strings.raising, T.inverse_weyl_one_single, Strings.step_single,
        hi, hj, hij, hji, hlast, T.pairing_reflection, T.weylEquiv_single_neg,
        T.weylEquiv_single_pos, T.weylEquiv_single_zero]
  · apply Finsupp.lhom_ext
    intro μ r
    change T.weylEquiv R i 1 (T.raising R j
        ((T.weylEquiv R i 1)⁻¹ (Finsupp.single μ r))) =
      -(T.raising R i (T.raising R j (T.raising R i (Finsupp.single μ r))))
    have hlast : T.pairing i (T.reflection j (T.reflection i μ)) =
        T.pairing i μ + 2 * T.pairing j μ := by
      rw [hji, T.pairing_reflection, hij]
      omega
    have hbound := T.minuscule i (T.reflection j μ)
    rw [hji] at hbound
    rcases T.minuscule i μ with hi | hi | hi <;>
      rcases T.minuscule j μ with hj | hj | hj
    all_goals try omega
    all_goals
      simp [Strings.raising, T.inverse_weyl_one_single, Strings.step_single,
        hi, hj, hij, hji, hlast, T.pairing_reflection, T.weylEquiv_single_neg,
        T.weylEquiv_single_pos, T.weylEquiv_single_zero]

private theorem strings_conjugate_root_toLinearMap
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R]
    (w : Strings.OrbitModule (Ω := Ω) R ≃ₗ[R] Strings.OrbitModule (Ω := Ω) R)
    (i : I) (t : R) :
    (w * T.rootEquiv R i (-1) (by decide) t * w⁻¹).toLinearMap =
      1 + t • (w.toLinearMap * T.raising R i * (w⁻¹).toLinearMap) := by
  have hinv : w.toLinearMap * (w⁻¹).toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    change w (w⁻¹ v) = v
    exact w.apply_symm_apply v
  change w.toLinearMap * (1 + t • T.raising R i) * (w⁻¹).toLinearMap = _
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hinv]

private theorem strings_doubleEdge_rootEquiv_commutator
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ)
    (hbab : T.raising R j * T.raising R i * T.raising R j = 0) (s t : R) :
    ⁅T.rootEquiv R i (-1) (by decide) s, T.rootEquiv R j (-1) (by decide) t⁆ =
      (T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) (-s * t) *
        (T.weylEquiv R j 1)⁻¹) *
      (T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s ^ 2 * t) *
        (T.weylEquiv R i 1)⁻¹) := by
  obtain ⟨hshort, hlong⟩ := strings_doubleEdge_weyl_pins T R i j hij hji
  have hfirst :
      (T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) (-s * t) *
        (T.weylEquiv R j 1)⁻¹).toLinearMap =
        1 + (s * t) • (T.raising R i * T.raising R j - T.raising R j * T.raising R i) := by
    rw [strings_conjugate_root_toLinearMap, hshort]
    simp only [neg_mul, neg_smul, smul_sub]
    module
  have hsecond :
      (T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s ^ 2 * t) *
        (T.weylEquiv R i 1)⁻¹).toLinearMap =
        1 + (s ^ 2 * t) • (-(T.raising R i * T.raising R j * T.raising R i)) := by
    rw [strings_conjugate_root_toLinearMap, hlong]
  have hright :
      ((T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) (-s * t) *
          (T.weylEquiv R j 1)⁻¹) *
        (T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s ^ 2 * t) *
          (T.weylEquiv R i 1)⁻¹)).toLinearMap =
      (1 + (s * t) • (T.raising R i * T.raising R j - T.raising R j * T.raising R i)) *
        (1 + (s ^ 2 * t) • (-(T.raising R i * T.raising R j * T.raising R i))) := by
    rw [LinearEquiv.coe_toLinearMap_mul, hfirst, hsecond]
  apply LinearEquiv.toLinearMap_injective
  rw [hright]
  change T.transvection R i (-1) s * T.transvection R j (-1) t *
    T.transvection R i (-1) (-s) * T.transvection R j (-1) (-t) = _
  exact Atlas.Algebra.squareZero_doubleEdge_commutator_factors
    (T.raising R i) (T.raising R j) (T.raising_square R i) (T.raising_square R j)
    hbab s t

/-- Grade reversal keeps the original indices and reflections. -/
private def doubleEdgeReversedStrings {I Ω : Type*} (T : Strings I Ω) : Strings I Ω where
  pairing i μ := -T.pairing i μ
  reflection := T.reflection
  involutive := T.involutive
  pairing_reflection i μ := by
    change -T.pairing i (T.reflection i μ) = -(-T.pairing i μ)
    rw [T.pairing_reflection]
  minuscule i μ := by
    change -T.pairing i μ = -1 ∨ -T.pairing i μ = 0 ∨ -T.pairing i μ = 1
    rcases T.minuscule i μ with h | h | h <;> omega

private theorem doubleEdgeReversedStrings_step {I Ω : Type*}
    (T : Strings I Ω) (R : Type*) [CommRing R] (i : I) (ε : ℤ) :
    (doubleEdgeReversedStrings T).step R i ε = T.step R i (-ε) := by
  apply Finsupp.lhom_ext
  intro μ r
  simp only [Strings.step_single]
  change (if -T.pairing i μ = ε then Finsupp.single (T.reflection i μ) r else 0) =
    (if T.pairing i μ = -ε then Finsupp.single (T.reflection i μ) r else 0)
  have h : -T.pairing i μ = ε ↔ T.pairing i μ = -ε := by omega
  simp only [h]

private theorem doubleEdgeReversedStrings_rootEquiv {I Ω : Type*}
    (T : Strings I Ω) (R : Type*) [CommRing R] (i : I)
    (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    (doubleEdgeReversedStrings T).rootEquiv R i ε hε t =
      T.rootEquiv R i (-ε) (neg_ne_zero.mpr hε) t := by
  apply LinearEquiv.toLinearMap_injective
  change 1 + t • (doubleEdgeReversedStrings T).step R i ε = 1 + t • T.step R i (-ε)
  rw [doubleEdgeReversedStrings_step]

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

private theorem weightOrbit_doubleEdge_grades (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    (∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ) ∧
    (∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ) := by
  constructor
  · intro μ
    change weightReflection P i μ.val (corootElement P j) =
      μ.val (corootElement P j) + μ.val (corootElement P i)
    simpa only [hij, mul_neg_one, sub_neg_eq_add] using
      weightReflection_other_grade P j i μ.val
  · intro μ
    change weightReflection P j μ.val (corootElement P i) =
      μ.val (corootElement P i) + 2 * μ.val (corootElement P j)
    rw [weightReflection_other_grade, hji]
    ring

/-- The actual minuscule positive double-edge word, including characteristics
2 and 3. The two conjugate factors have parameters −s*t and s²*t. -/
theorem weightOrbit_doubleEdge_rootEquiv_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    ⁅T.rootEquiv R i (-1) (by decide) s, T.rootEquiv R j (-1) (by decide) t⁆ =
      (T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) (-s * t) *
        (T.weylEquiv R j 1)⁻¹) *
      (T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) (s ^ 2 * t) *
        (T.weylEquiv R i 1)⁻¹) := by
  obtain ⟨hgrade1, hgrade2⟩ := weightOrbit_doubleEdge_grades P S hc hm i j hij hji
  exact strings_doubleEdge_rootEquiv_commutator (stringsOfWeightOrbit P S hc hm) R i j
    hgrade1 hgrade2
    (weightOrbit_doubleEdge_reverse_sandwich P S hc hm R i j hij (-1) (by decide)) s t

/-- The negative double-edge word uses grade reversal on the same weight
set. No weight-negation closure or whole-companion opposition is assumed. -/
theorem weightOrbit_doubleEdge_lowering_rootEquiv_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (s t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    let V (k : ι) := T.rootEquiv R k 1 (by decide) 1 *
      T.rootEquiv R k (-1) (by decide) (-1) * T.rootEquiv R k 1 (by decide) 1
    ⁅T.rootEquiv R i 1 (by decide) s, T.rootEquiv R j 1 (by decide) t⁆ =
      (V j * T.rootEquiv R i 1 (by decide) (-s * t) * (V j)⁻¹) *
      (V i * T.rootEquiv R j 1 (by decide) (s ^ 2 * t) * (V i)⁻¹) := by
  let T := stringsOfWeightOrbit P S hc hm
  obtain ⟨hgrade1, hgrade2⟩ := weightOrbit_doubleEdge_grades P S hc hm i j hij hji
  have hrev1 (μ) :
      (doubleEdgeReversedStrings T).pairing j ((doubleEdgeReversedStrings T).reflection i μ) =
        (doubleEdgeReversedStrings T).pairing j μ + (doubleEdgeReversedStrings T).pairing i μ := by
    change -T.pairing j (T.reflection i μ) = -T.pairing j μ + -T.pairing i μ
    rw [hgrade1]
    dsimp only [T]
    omega
  have hrev2 (μ) :
      (doubleEdgeReversedStrings T).pairing i ((doubleEdgeReversedStrings T).reflection j μ) =
        (doubleEdgeReversedStrings T).pairing i μ + 2 * (doubleEdgeReversedStrings T).pairing j μ := by
    change -T.pairing i (T.reflection j μ) = -T.pairing i μ + 2 * -T.pairing j μ
    rw [hgrade2]
    dsimp only [T]
    omega
  have hbab : (doubleEdgeReversedStrings T).raising R j *
      (doubleEdgeReversedStrings T).raising R i * (doubleEdgeReversedStrings T).raising R j = 0 := by
    simpa only [Strings.raising, doubleEdgeReversedStrings_step, neg_neg, T] using
      weightOrbit_doubleEdge_reverse_sandwich P S hc hm R i j hij 1 (by decide)
  have h := strings_doubleEdge_rootEquiv_commutator
    (doubleEdgeReversedStrings T) R i j hrev1 hrev2 hbab s t
  simpa only [T, Strings.weylEquiv, doubleEdgeReversedStrings_rootEquiv, neg_neg,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h

/-- Equality of the actual positive matrix units on the finite weight set. -/
theorem weightOrbit_doubleEdge_rootElements_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (s t : R) :
    let W (k : ι) := weightOrbitRootElement P S hc hm R k (-1) (by decide) 1 *
      weightOrbitRootElement P S hc hm R k 1 (by decide) (-1) *
        weightOrbitRootElement P S hc hm R k (-1) (by decide) 1
    ⁅weightOrbitRootElement P S hc hm R i (-1) (by decide) s,
        weightOrbitRootElement P S hc hm R j (-1) (by decide) t⁆ =
      (W j * weightOrbitRootElement P S hc hm R i (-1) (by decide) (-s * t) * (W j)⁻¹) *
      (W i * weightOrbitRootElement P S hc hm R j (-1) (by decide) (s ^ 2 * t) * (W i)⁻¹) := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_doubleEdge_rootEquiv_commutator P S hc hm R i j hij hji s t)
  simpa only [weightOrbitRootElement, map_commutatorElement, map_mul, map_inv,
    Strings.equivMatrixHom_root, Strings.equivMatrixHom_weyl, Strings.weylMatrixUnit,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h

/-- Equality of the actual negative matrix units on the same finite weights. -/
theorem weightOrbit_doubleEdge_lowering_rootElements_commutator (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (s t : R) :
    let V (k : ι) := weightOrbitRootElement P S hc hm R k 1 (by decide) 1 *
      weightOrbitRootElement P S hc hm R k (-1) (by decide) (-1) *
        weightOrbitRootElement P S hc hm R k 1 (by decide) 1
    ⁅weightOrbitRootElement P S hc hm R i 1 (by decide) s,
        weightOrbitRootElement P S hc hm R j 1 (by decide) t⁆ =
      (V j * weightOrbitRootElement P S hc hm R i 1 (by decide) (-s * t) * (V j)⁻¹) *
      (V i * weightOrbitRootElement P S hc hm R j 1 (by decide) (s ^ 2 * t) * (V i)⁻¹) := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_doubleEdge_lowering_rootEquiv_commutator P S hc hm R i j hij hji s t)
  simpa only [weightOrbitRootElement, map_commutatorElement, map_mul, map_inv,
    Strings.equivMatrixHom_root] using h

end Atlas.Chevalley.Integral.Minuscule
