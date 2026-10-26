import Atlas.LinearGroups.Chevalley.Integral.MinusculeDoubleEdgeWord

/-! Signed marked short-middle B2 normalization on the original minuscule
weight sets. The calculation is integral, with no weight-negation hypothesis. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

private theorem strings_b2_short_pin
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ) :
    (T.weylEquiv R j 1).toLinearMap * T.raising R i *
        ((T.weylEquiv R j 1)⁻¹).toLinearMap =
      T.raising R j * T.raising R i - T.raising R i * T.raising R j := by
  apply Finsupp.lhom_ext
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

private theorem strings_b2_short_middle_negated
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ) :
    (T.weylEquiv R i 1).toLinearMap *
        (T.raising R j * T.raising R i - T.raising R i * T.raising R j) *
        ((T.weylEquiv R i 1)⁻¹).toLinearMap =
      -(T.raising R j * T.raising R i - T.raising R i * T.raising R j) := by
  apply Finsupp.lhom_ext
  intro μ r
  change T.weylEquiv R i 1
      (T.raising R j (T.raising R i ((T.weylEquiv R i 1)⁻¹ (Finsupp.single μ r))) -
        T.raising R i (T.raising R j ((T.weylEquiv R i 1)⁻¹ (Finsupp.single μ r)))) =
    -(T.raising R j (T.raising R i (Finsupp.single μ r)) -
      T.raising R i (T.raising R j (Finsupp.single μ r)))
  have hbound := T.minuscule i (T.reflection j μ)
  rw [hji] at hbound
  rcases T.minuscule i μ with hi | hi | hi <;>
    rcases T.minuscule j μ with hj | hj | hj
  all_goals try omega
  all_goals
    simp [Strings.raising, T.inverse_weyl_one_single, Strings.step_single,
      hi, hj, hij, hji, T.pairing_reflection,
      T.weylEquiv_single_neg, T.weylEquiv_single_pos, T.weylEquiv_single_zero]
  all_goals
    simp only [T.involutive i μ, T.involutive i (T.reflection j (T.reflection i μ))]

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

private theorem marked_short_b2_grades (i j : ι)
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

theorem weightOrbit_b2_weyl_conjugate_raising_short (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    (T.weylEquiv R j 1).toLinearMap * T.raising R i *
        ((T.weylEquiv R j 1)⁻¹).toLinearMap =
      T.raising R j * T.raising R i - T.raising R i * T.raising R j := by
  obtain ⟨h1, h2⟩ := marked_short_b2_grades P S hc hm i j hij hji
  exact strings_b2_short_pin (stringsOfWeightOrbit P S hc hm) R i j h1 h2

theorem weightOrbit_b2_weyl_negates_short_middle (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    (T.weylEquiv R i 1).toLinearMap *
        (T.raising R j * T.raising R i - T.raising R i * T.raising R j) *
        ((T.weylEquiv R i 1)⁻¹).toLinearMap =
      -(T.raising R j * T.raising R i - T.raising R i * T.raising R j) := by
  obtain ⟨h1, h2⟩ := marked_short_b2_grades P S hc hm i j hij hji
  exact strings_b2_short_middle_negated (stringsOfWeightOrbit P S hc hm) R i j h1 h2

/-- The parameter sign is explicit in the actual linear equivalences. -/
theorem weightOrbit_b2_weyl_negates_short_conjugate_rootEquiv (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylEquiv R i 1 *
        (T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) t *
          (T.weylEquiv R j 1)⁻¹) * (T.weylEquiv R i 1)⁻¹ =
      T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) (-t) *
        (T.weylEquiv R j 1)⁻¹ := by
  let T := stringsOfWeightOrbit P S hc hm
  let C := T.raising R j * T.raising R i - T.raising R i * T.raising R j
  let Z (s : R) := T.weylEquiv R j 1 * T.rootEquiv R i (-1) (by decide) s *
    (T.weylEquiv R j 1)⁻¹
  have hpin := weightOrbit_b2_weyl_conjugate_raising_short P S hc hm R i j hij hji
  dsimp only at hpin
  have hneg := weightOrbit_b2_weyl_negates_short_middle P S hc hm R i j hij hji
  dsimp only at hneg
  have hinv (k : ι) : (T.weylEquiv R k 1).toLinearMap *
      ((T.weylEquiv R k 1)⁻¹).toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    exact (T.weylEquiv R k 1).apply_symm_apply v
  have hroot (s : R) : (Z s).toLinearMap = 1 + s • C := by
    change (T.weylEquiv R j 1).toLinearMap * (1 + s • T.raising R i) *
      ((T.weylEquiv R j 1)⁻¹).toLinearMap = _
    simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hinv]
    rw [hpin]
  apply LinearEquiv.toLinearMap_injective
  change (T.weylEquiv R i 1).toLinearMap * (Z t).toLinearMap *
    ((T.weylEquiv R i 1)⁻¹).toLinearMap = (Z (-t)).toLinearMap
  rw [hroot, hroot]
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hinv]
  change 1 + t • ((T.weylEquiv R i 1).toLinearMap * C *
    ((T.weylEquiv R i 1)⁻¹).toLinearMap) = 1 + (-t) • C
  rw [hneg]
  apply LinearMap.ext
  intro v
  change v + t • (-(C v)) = v + (-t) • C v
  simp only [smul_neg, neg_smul]

theorem weightOrbit_b2_weyl_negates_short_conjugate_rootElements (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (t : R) :
    let W (k : ι) := weightOrbitRootElement P S hc hm R k (-1) (by decide) 1 *
      weightOrbitRootElement P S hc hm R k 1 (by decide) (-1) *
        weightOrbitRootElement P S hc hm R k (-1) (by decide) 1
    W i * (W j * weightOrbitRootElement P S hc hm R i (-1) (by decide) t * (W j)⁻¹) *
        (W i)⁻¹ = W j * weightOrbitRootElement P S hc hm R i (-1) (by decide) (-t) * (W j)⁻¹ := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_b2_weyl_negates_short_conjugate_rootEquiv P S hc hm R i j hij hji t)
  simpa only [weightOrbitRootElement, map_mul, map_inv,
    Strings.equivMatrixHom_root, Strings.equivMatrixHom_weyl, Strings.weylMatrixUnit,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h

end Atlas.Chevalley.Integral.Minuscule
