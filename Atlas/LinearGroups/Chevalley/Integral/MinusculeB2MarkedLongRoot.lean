import Atlas.LinearGroups.Chevalley.Integral.MinusculeDoubleEdgeWord

/-! The marked B2 long-root normalization on the actual minuscule blocks.
This proof is integral: the nonzero sandwich has both endpoints of long-node
grade zero, where that Weyl operator acts as the identity. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

private theorem strings_b2_long_pin
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ) :
    (T.weylEquiv R i 1).toLinearMap * T.raising R j *
        ((T.weylEquiv R i 1)⁻¹).toLinearMap =
      -(T.raising R i * T.raising R j * T.raising R i) := by
  apply Finsupp.lhom_ext
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

private theorem strings_b2_long_sandwich_commute
    {I Ω : Type*} (T : Strings I Ω) (R : Type*) [CommRing R] (i j : I)
    (hij : ∀ μ, T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ)
    (hji : ∀ μ, T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ) :
    Commute (T.weylEquiv R j 1).toLinearMap
      (T.raising R i * T.raising R j * T.raising R i) := by
  change _ * _ = _ * _
  apply Finsupp.lhom_ext
  intro μ r
  change T.weylEquiv R j 1
      (T.raising R i (T.raising R j (T.raising R i (Finsupp.single μ r)))) =
    T.raising R i (T.raising R j (T.raising R i
      (T.weylEquiv R j 1 (Finsupp.single μ r))))
  have hlast (ν : Ω) :
      T.pairing j (T.reflection i (T.reflection j (T.reflection i ν))) = T.pairing j ν := by
    simp only [hij, hji, T.pairing_reflection]
    omega
  have hbound := T.minuscule i (T.reflection j μ)
  rw [hji] at hbound
  rcases T.minuscule i μ with hi | hi | hi <;>
    rcases T.minuscule j μ with hj | hj | hj
  all_goals try omega
  all_goals
    simp [Strings.raising, Strings.step_single, hi, hj, hij, hji, hlast,
      T.pairing_reflection, T.weylEquiv_single_neg, T.weylEquiv_single_pos,
      T.weylEquiv_single_zero]

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

private theorem marked_b2_grades (i j : ι)
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

/-- The actual long-root operator is the negative square-zero sandwich. -/
theorem weightOrbit_b2_weyl_conjugate_raising_long (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    (T.weylEquiv R i 1).toLinearMap * T.raising R j *
      ((T.weylEquiv R i 1)⁻¹).toLinearMap =
        -(T.raising R i * T.raising R j * T.raising R i) := by
  obtain ⟨h1, h2⟩ := marked_b2_grades P S hc hm i j hij hji
  exact strings_b2_long_pin (stringsOfWeightOrbit P S hc hm) R i j h1 h2

/-- The long simple Weyl element fixes both endpoints of the nonzero
long-root sandwich, over any coefficient ring. -/
theorem weightOrbit_b2_long_sandwich_commute (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    Commute (T.weylEquiv R j 1).toLinearMap
      (T.raising R i * T.raising R j * T.raising R i) := by
  obtain ⟨h1, h2⟩ := marked_b2_grades P S hc hm i j hij hji
  exact strings_b2_long_sandwich_commute (stringsOfWeightOrbit P S hc hm) R i j h1 h2

/-- The literal linear equivalences satisfy the marked long-root identity. -/
theorem weightOrbit_b2_weyl_fixes_long_conjugate_rootEquiv (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (t : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylEquiv R j 1 *
        (T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) t *
          (T.weylEquiv R i 1)⁻¹) * (T.weylEquiv R j 1)⁻¹ =
      T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) t *
        (T.weylEquiv R i 1)⁻¹ := by
  let T := stringsOfWeightOrbit P S hc hm
  let Z := T.weylEquiv R i 1 * T.rootEquiv R j (-1) (by decide) t *
    (T.weylEquiv R i 1)⁻¹
  have hpin := weightOrbit_b2_weyl_conjugate_raising_long P S hc hm R i j hij hji
  dsimp only at hpin
  have hinv : (T.weylEquiv R i 1).toLinearMap *
      ((T.weylEquiv R i 1)⁻¹).toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    exact (T.weylEquiv R i 1).apply_symm_apply v
  have hroot : Z.toLinearMap =
      1 + t • (-(T.raising R i * T.raising R j * T.raising R i)) := by
    change (T.weylEquiv R i 1).toLinearMap * (1 + t • T.raising R j) *
      ((T.weylEquiv R i 1)⁻¹).toLinearMap = _
    simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hinv]
    rw [hpin]
  have hcomm : Commute (T.weylEquiv R j 1) Z := by
    change T.weylEquiv R j 1 * Z = Z * T.weylEquiv R j 1
    apply LinearEquiv.toLinearMap_injective
    change (T.weylEquiv R j 1).toLinearMap * Z.toLinearMap =
      Z.toLinearMap * (T.weylEquiv R j 1).toLinearMap
    rw [hroot]
    have hD := (weightOrbit_b2_long_sandwich_commute P S hc hm R i j hij hji).eq
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun f : Module.End R (Strings.OrbitModule
      (Ω := WeightOrbit P S) R) => f v) hD
    simp only [Module.End.mul_apply] at hv
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, LinearMap.neg_apply, map_add, map_smul, map_neg]
    rw [hv] <;> rfl
  change T.weylEquiv R j 1 * Z * (T.weylEquiv R j 1)⁻¹ = Z
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- The same equality for actual minuscule matrix units. -/
theorem weightOrbit_b2_weyl_fixes_long_conjugate_rootElements (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) (t : R) :
    let W (k : ι) := weightOrbitRootElement P S hc hm R k (-1) (by decide) 1 *
      weightOrbitRootElement P S hc hm R k 1 (by decide) (-1) *
        weightOrbitRootElement P S hc hm R k (-1) (by decide) 1
    W j * (W i * weightOrbitRootElement P S hc hm R j (-1) (by decide) t * (W i)⁻¹) *
        (W j)⁻¹ = W i * weightOrbitRootElement P S hc hm R j (-1) (by decide) t * (W i)⁻¹ := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_b2_weyl_fixes_long_conjugate_rootEquiv P S hc hm R i j hij hji t)
  simpa only [weightOrbitRootElement, map_mul, map_inv,
    Strings.equivMatrixHom_root, Strings.equivMatrixHom_weyl, Strings.weylMatrixUnit,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h

end Atlas.Chevalley.Integral.Minuscule
