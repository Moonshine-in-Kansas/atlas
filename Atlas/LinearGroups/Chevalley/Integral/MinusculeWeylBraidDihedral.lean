import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylBraidA2

/-! Length-four and length-six braid identities on literal reflection-closed
minuscule weight sets. Both the weight labels and all signed coefficients
are compared directly over arbitrary commutative rings. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]

theorem weightReflection_b2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2)
    (μ : WeightLattice P) :
    weightReflection P i (weightReflection P j (weightReflection P i (weightReflection P j (μ)))) =
      weightReflection P j (weightReflection P i (weightReflection P j (weightReflection P i (μ)))) := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  ext x
  simp only [weightReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, rootWeight_corootElement, P.pairing_same, hpij, hpji]
  ring

theorem weightReflection_g2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3)
    (μ : WeightLattice P) :
    weightReflection P i (weightReflection P j (weightReflection P i (weightReflection P j (weightReflection P i (weightReflection P j (μ)))))) =
      weightReflection P j (weightReflection P i (weightReflection P j (weightReflection P i (weightReflection P j (weightReflection P i (μ)))))) := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  ext x
  simp only [weightReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, rootWeight_corootElement, P.pairing_same, hpij, hpji]
  ring

variable (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- The signed operators agree, not only their underlying weight permutations. -/
theorem weightOrbit_weylEquiv_b2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 =
      T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 := by
  let T := stringsOfWeightOrbit P S hc hm
  have hgradeij (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ := by
    change (weightReflection P i μ.val) (corootElement P j) =
      μ.val (corootElement P j) + μ.val (corootElement P i)
    simpa only [hij, mul_neg_one, sub_neg_eq_add] using
      weightReflection_other_grade P j i μ.val
  have hgradeji (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j μ) = T.pairing i μ + 2 * T.pairing j μ := by
    change (weightReflection P j μ.val) (corootElement P i) =
      μ.val (corootElement P i) + 2 * μ.val (corootElement P j)
    rw [weightReflection_other_grade, hji]
    ring
  have hgrade2i (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i (μ))) = T.pairing i μ + 2 * T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade2j (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j (μ))) = T.pairing i μ + T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade3i (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i (T.reflection j (μ)))) = T.pairing i μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade3j (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j (T.reflection i (μ)))) = T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hlabels (μ : WeightOrbit P S) :
      T.reflection i (T.reflection j (T.reflection i (T.reflection j (μ)))) =
        T.reflection j (T.reflection i (T.reflection j (T.reflection i (μ)))) :=
    Subtype.ext (weightReflection_b2_braid P i j hij hji μ.val)
  have hsigned (k : ι) (μ : WeightOrbit P S) (r : R) :
      T.weylEquiv R k 1 (Finsupp.single μ r) =
        Finsupp.single (T.reflection k μ)
          ((if T.pairing k μ = 1 then (-1 : R) else 1) * r) :=
    weightOrbit_weyl_one_single_signed P S hc hm R k μ r
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  change T.weylEquiv R i 1 (T.weylEquiv R j 1 (T.weylEquiv R i 1 (T.weylEquiv R j 1 (Finsupp.single μ r)))) =
    T.weylEquiv R j 1 (T.weylEquiv R i 1 (T.weylEquiv R j 1 (T.weylEquiv R i 1 (Finsupp.single μ r))))
  simp only [hsigned, hlabels, hgrade3j, hgrade3i, hgrade2j, hgrade2i, hgradeij, hgradeji]
  simp only [add_comm, mul_comm, mul_left_comm, mul_assoc]

/-- The actual matrix units satisfy the same braid over every commutative ring. -/
theorem weightOrbit_weylMatrixUnit_b2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 =
      T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_weylEquiv_b2_braid P S hc hm R i j hij hji)
  simpa only [map_mul, Strings.equivMatrixHom_weyl] using h

set_option maxHeartbeats 1000000 in
/-- The signed operators agree, not only their underlying weight permutations. -/
theorem weightOrbit_weylEquiv_g2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 =
      T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 := by
  let T := stringsOfWeightOrbit P S hc hm
  have hgradeij (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ := by
    change (weightReflection P i μ.val) (corootElement P j) =
      μ.val (corootElement P j) + μ.val (corootElement P i)
    simpa only [hij, mul_neg_one, sub_neg_eq_add] using
      weightReflection_other_grade P j i μ.val
  have hgradeji (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j μ) = T.pairing i μ + 3 * T.pairing j μ := by
    change (weightReflection P j μ.val) (corootElement P i) =
      μ.val (corootElement P i) + 3 * μ.val (corootElement P j)
    rw [weightReflection_other_grade, hji]
    ring
  have hgrade2i (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i (μ))) = 2 * T.pairing i μ + 3 * T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade2j (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j (μ))) = T.pairing i μ + 2 * T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade3i (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i (T.reflection j (μ)))) = 2 * T.pairing i μ + 3 * T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade3j (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j (T.reflection i (μ)))) = T.pairing i μ + 2 * T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade4i (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i (T.reflection j (T.reflection i (μ))))) = T.pairing i μ + 3 * T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade4j (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j (T.reflection i (T.reflection j (μ))))) = T.pairing i μ + T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade5i (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i (T.reflection j (T.reflection i (T.reflection j (μ)))))) = T.pairing i μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hgrade5j (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j (T.reflection i (T.reflection j (T.reflection i (μ)))))) = T.pairing j μ := by
    simp only [hgradeij, hgradeji, T.pairing_reflection]
    omega
  have hlabels (μ : WeightOrbit P S) :
      T.reflection i (T.reflection j (T.reflection i (T.reflection j (T.reflection i (T.reflection j (μ)))))) =
        T.reflection j (T.reflection i (T.reflection j (T.reflection i (T.reflection j (T.reflection i (μ)))))) :=
    Subtype.ext (weightReflection_g2_braid P i j hij hji μ.val)
  have hsigned (k : ι) (μ : WeightOrbit P S) (r : R) :
      T.weylEquiv R k 1 (Finsupp.single μ r) =
        Finsupp.single (T.reflection k μ)
          ((if T.pairing k μ = 1 then (-1 : R) else 1) * r) :=
    weightOrbit_weyl_one_single_signed P S hc hm R k μ r
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  change T.weylEquiv R i 1 (T.weylEquiv R j 1 (T.weylEquiv R i 1 (T.weylEquiv R j 1 (T.weylEquiv R i 1 (T.weylEquiv R j 1 (Finsupp.single μ r)))))) =
    T.weylEquiv R j 1 (T.weylEquiv R i 1 (T.weylEquiv R j 1 (T.weylEquiv R i 1 (T.weylEquiv R j 1 (T.weylEquiv R i 1 (Finsupp.single μ r))))))
  simp only [hsigned, hlabels, hgrade5j, hgrade5i, hgrade4j, hgrade4i, hgrade3j, hgrade3i, hgrade2j, hgrade2i, hgradeij, hgradeji]
  simp only [add_comm, mul_comm, mul_left_comm, mul_assoc]

/-- The actual matrix units satisfy the same braid over every commutative ring. -/
theorem weightOrbit_weylMatrixUnit_g2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 =
      T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_weylEquiv_g2_braid P S hc hm R i j hij hji)
  simpa only [map_mul, Strings.equivMatrixHom_weyl] using h

end Atlas.Chevalley.Integral.Minuscule
