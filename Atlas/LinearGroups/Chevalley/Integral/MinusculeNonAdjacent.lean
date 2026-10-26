import Atlas.LinearGroups.Chevalley.Integral.MinusculeOpposite

/-! Source candidate: commuting actual minuscule steps and root matrices at
zero pairings, for arbitrary signs and all commutative coefficient rings. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)

/-- At orthogonal root labels, both grades are unchanged by the other reflection.
The step signs need not be opposite, or even nonzero, in this operator identity. -/
theorem weightOrbit_steps_commute_of_zero
    (i j : ι) (hij : P.pairingIn ℤ i j = 0) (hji : P.pairingIn ℤ j i = 0)
    (R : Type*) [CommRing R] (ε δ : ℤ) :
    Commute ((stringsOfWeightOrbit P S hc hm).step R i ε)
      ((stringsOfWeightOrbit P S hc hm).step R j δ) := by
  let T := stringsOfWeightOrbit P S hc hm
  have grade (a c : ι) (μ : WeightOrbit P S) :
      T.pairing a (T.reflection c μ) =
        T.pairing a μ - T.pairing c μ * P.pairingIn ℤ c a :=
    weightReflection_other_grade P a c μ.val
  change T.step R i ε * T.step R j δ = T.step R j δ * T.step R i ε
  apply Finsupp.lhom_ext
  intro μ r
  change T.step R i ε (T.step R j δ (Finsupp.single μ r)) =
    T.step R j δ (T.step R i ε (Finsupp.single μ r))
  have hi : T.pairing i (T.reflection j μ) = T.pairing i μ := by
    rw [grade, hji, mul_zero, sub_zero]
  have hj : T.pairing j (T.reflection i μ) = T.pairing j μ := by
    rw [grade, hij, mul_zero, sub_zero]
  have href : T.reflection i (T.reflection j μ) = T.reflection j (T.reflection i μ) :=
    Subtype.ext (weightReflections_commute_of_zero P i j hij hji μ.val)
  by_cases hmi : T.pairing i μ = ε <;>
    by_cases hmj : T.pairing j μ = δ <;> simp [hmi, hmj, hi, hj, href]

theorem weightOrbit_stepMatrices_commute_of_zero
    (i j : ι) (hij : P.pairingIn ℤ i j = 0) (hji : P.pairingIn ℤ j i = 0)
    (R : Type*) [CommRing R] (ε δ : ℤ) :
    Commute ((stringsOfWeightOrbit P S hc hm).stepMatrix R i ε)
      ((stringsOfWeightOrbit P S hc hm).stepMatrix R j δ) := by
  have h := congrArg (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne)
    (weightOrbit_steps_commute_of_zero P S hc hm i j hij hji R ε δ).eq
  change _ * _ = _ * _
  simpa only [LinearMap.toMatrix_mul, Strings.stepMatrix] using h

/-- Actual invertible root matrices; the nonzero signs supply their inverses. -/
theorem weightOrbit_rootElements_commute_of_zero
    (i j : ι) (hij : P.pairingIn ℤ i j = 0) (hji : P.pairingIn ℤ j i = 0)
    (R : Type*) [CommRing R] (ε δ : ℤ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (s t : R) :
    Commute (weightOrbitRootElement P S hc hm R i ε hε s)
      (weightOrbitRootElement P S hc hm R j δ hδ t) := by
  have h := ((weightOrbit_stepMatrices_commute_of_zero P S hc hm
    i j hij hji R ε δ).smul_left s).smul_right t
  change _ * _ = _ * _
  apply Units.ext
  change (1 + s • (stringsOfWeightOrbit P S hc hm).stepMatrix R i ε) *
      (1 + t • (stringsOfWeightOrbit P S hc hm).stepMatrix R j δ) =
    (1 + t • (stringsOfWeightOrbit P S hc hm).stepMatrix R j δ) *
      (1 + s • (stringsOfWeightOrbit P S hc hm).stepMatrix R i ε)
  exact ((Commute.one_right _).add_right ((Commute.one_left _).add_left h)).eq

end Atlas.Chevalley.Integral.Minuscule
