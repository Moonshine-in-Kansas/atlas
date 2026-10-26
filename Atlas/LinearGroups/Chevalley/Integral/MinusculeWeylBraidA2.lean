import Atlas.LinearGroups.Chevalley.Integral.MinusculeOpposite
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation

/-! Source candidate: the actual signed minuscule Weyl operators satisfy the
A2 braid on every weight in its original reflection-closed orbit. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]

theorem weightReflection_a2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1)
    (μ : WeightLattice P) :
    weightReflection P i (weightReflection P j (weightReflection P i μ)) =
      weightReflection P j (weightReflection P i (weightReflection P j μ)) := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -1 := by
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

/-- Actual grade-zero weights are fixed by reflection, so the three installed
Weyl formulas combine into one formula on the literal weight orbit. -/
theorem weightOrbit_weyl_one_single_signed (i : ι) (μ : WeightOrbit P S) (r : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylEquiv R i 1 (Finsupp.single μ r) =
      Finsupp.single (T.reflection i μ)
        ((if T.pairing i μ = 1 then (-1 : R) else 1) * r) := by
  let T := stringsOfWeightOrbit P S hc hm
  change T.weylEquiv R i 1 (Finsupp.single μ r) =
    Finsupp.single (T.reflection i μ)
      ((if T.pairing i μ = 1 then (-1 : R) else 1) * r)
  rcases T.minuscule i μ with hi | hi | hi
  · rw [T.weylEquiv_single_neg R i 1 μ r hi]
    simp [hi]
  · have hr : T.reflection i μ = μ :=
      Subtype.ext (weightReflection_fixed_of_zero P i μ.val hi)
    rw [T.weylEquiv_single_zero R i 1 μ r hi, hr]
    simp [hi]
  · rw [T.weylEquiv_single_pos R i 1 μ r hi]
    simp [hi]

theorem weightOrbit_weylEquiv_a2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylEquiv R i 1 * T.weylEquiv R j 1 * T.weylEquiv R i 1 =
      T.weylEquiv R j 1 * T.weylEquiv R i 1 * T.weylEquiv R j 1 := by
  let T := stringsOfWeightOrbit P S hc hm
  have hgradeij (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i μ) = T.pairing j μ + T.pairing i μ := by
    change (weightReflection P i μ.val) (corootElement P j) =
      μ.val (corootElement P j) + μ.val (corootElement P i)
    simpa only [hij, mul_neg_one, sub_neg_eq_add] using
      weightReflection_other_grade P j i μ.val
  have hgradeji (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j μ) = T.pairing i μ + T.pairing j μ := by
    change (weightReflection P j μ.val) (corootElement P i) =
      μ.val (corootElement P i) + μ.val (corootElement P j)
    simpa only [hji, mul_neg_one, sub_neg_eq_add] using
      weightReflection_other_grade P i j μ.val
  have hlastij (μ : WeightOrbit P S) :
      T.pairing i (T.reflection j (T.reflection i μ)) = T.pairing j μ := by
    rw [hgradeji, T.pairing_reflection, hgradeij]
    omega
  have hlastji (μ : WeightOrbit P S) :
      T.pairing j (T.reflection i (T.reflection j μ)) = T.pairing i μ := by
    rw [hgradeij, T.pairing_reflection, hgradeji]
    omega
  have hlabels (μ : WeightOrbit P S) :
      T.reflection i (T.reflection j (T.reflection i μ)) =
        T.reflection j (T.reflection i (T.reflection j μ)) :=
    Subtype.ext (weightReflection_a2_braid P i j hij hji μ.val)
  have hsigned (k : ι) (μ : WeightOrbit P S) (r : R) :
      T.weylEquiv R k 1 (Finsupp.single μ r) =
        Finsupp.single (T.reflection k μ)
          ((if T.pairing k μ = 1 then (-1 : R) else 1) * r) :=
    weightOrbit_weyl_one_single_signed P S hc hm R k μ r
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  change T.weylEquiv R i 1 (T.weylEquiv R j 1
      (T.weylEquiv R i 1 (Finsupp.single μ r))) =
    T.weylEquiv R j 1 (T.weylEquiv R i 1
      (T.weylEquiv R j 1 (Finsupp.single μ r)))
  simp only [hsigned, hlabels, hlastij, hlastji, hgradeij, hgradeji]
  simp only [add_comm, mul_comm, mul_left_comm, mul_assoc]

/-- Equality of the actual units, not only of their associated permutations. -/
theorem weightOrbit_weylMatrixUnit_a2_braid (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -1) :
    let T := stringsOfWeightOrbit P S hc hm
    T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 =
      T.weylMatrixUnit R j 1 * T.weylMatrixUnit R i 1 * T.weylMatrixUnit R j 1 := by
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_weylEquiv_a2_braid P S hc hm R i j hij hji)
  simpa only [map_mul, Strings.equivMatrixHom_weyl] using h

end Atlas.Chevalley.Integral.Minuscule
