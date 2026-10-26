import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation
import Atlas.LinearGroups.Chevalley.Integral.MinusculeOpposite
/-! Actual cross-root torus scaling, without a Lie
intertwiner or central-kernel premise. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

theorem weightOrbit_torusEquiv_mul_root (i j : ι) (ε : ℤ) (hε : ε ≠ 0)
    (a : Rˣ) (s : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.torusEquiv R j a * T.rootEquiv R i ε hε s =
      T.rootEquiv R i ε hε ((a ^ (-ε * P.pairingIn ℤ i j)).val*s) * T.torusEquiv R j a := by
  let T := stringsOfWeightOrbit P S hc hm
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply, LinearEquiv.coe_coe]
  by_cases h : T.pairing i μ = ε
  · have hg : T.pairing j (T.reflection i μ) =
        T.pairing j μ + (-ε * P.pairingIn ℤ i j) := by
      rw [show T.pairing j (T.reflection i μ) =
        T.pairing j μ - T.pairing i μ * P.pairingIn ℤ i j from
          weightReflection_other_grade P j i μ.val, h]
      ring
    have hp : P.pairing i j = P.pairingIn ℤ i j := by
      simpa using (P.algebraMap_pairingIn ℤ i j).symm
    dsimp only [T, stringsOfWeightOrbit] at h hg
    simp [Strings.rootEquiv, Strings.transvection_apply, Strings.step_single, h,
      Strings.torusEquiv_single, hg, map_add, map_smul, Finsupp.smul_single, smul_eq_mul,
      hp, sub_eq_add_neg, zpow_add, zpow_neg, Units.val_mul, mul_assoc, mul_left_comm, mul_comm]
  · dsimp only [T, stringsOfWeightOrbit] at h
    simp [Strings.rootEquiv, Strings.transvection_apply, Strings.step_single, h,
      Strings.torusEquiv_single]

theorem weightOrbit_torusMatrixUnit_mul_root (i j : ι) (ε : ℤ) (hε : ε ≠ 0)
    (a : Rˣ) (s : R) :
    let T := stringsOfWeightOrbit P S hc hm
    T.torusMatrixUnit R j a * T.rootMatrixUnit R i ε hε s =
      T.rootMatrixUnit R i ε hε ((a ^ (-ε * P.pairingIn ℤ i j)).val*s) * T.torusMatrixUnit R j a := by
  let T := stringsOfWeightOrbit P S hc hm
  have h := congrArg (Strings.equivMatrixHom R)
    (weightOrbit_torusEquiv_mul_root P S hc hm R i j ε hε a s)
  simpa only [map_mul, Strings.equivMatrixHom_root, Strings.equivMatrixHom_torus] using h
end Atlas.Chevalley.Integral.Minuscule
