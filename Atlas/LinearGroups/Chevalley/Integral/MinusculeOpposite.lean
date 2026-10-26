import Atlas.LinearGroups.Chevalley.Integral.MinusculeOrbitRepresentation
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Opposite distinct simple operators on actual minuscule weights.
No irreducibility, reducedness, rank bound, or characteristic restriction is used.
The minuscule and reflection-closure hypotheses concern the literal integral
weight subset; no group relation or target-group result is supplied. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)

/-- Row j, column i is the coefficient subtracted from the i-grade by reflection j. -/
theorem weightReflection_other_grade (i j : ι) (μ : WeightLattice P) :
    weightReflection P j μ (corootElement P i) =
      μ (corootElement P i) - μ (corootElement P j) * P.pairingIn ℤ j i := by
  have hp : P.pairing j i = P.pairingIn ℤ j i := by
    simpa using (P.algebraMap_pairingIn ℤ j i).symm
  simp [weightReflection_apply, rootWeight_corootElement, hp]

theorem weightReflections_commute_of_zero (i j : ι)
    (hij : P.pairingIn ℤ i j = 0) (hji : P.pairingIn ℤ j i = 0)
    (μ : WeightLattice P) :
    weightReflection P i (weightReflection P j μ) =
      weightReflection P j (weightReflection P i μ) := by
  have hij' : P.pairing i j = 0 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij, map_zero]
  have hji' : P.pairing j i = 0 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji, map_zero]
  ext x
  simp only [weightReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, rootWeight_corootElement, hij', hji', mul_zero, sub_zero]
  ring

/-- Genuine operator commutation; no representation relation is supplied as input. -/
theorem weightOrbit_opposite_steps_commute (b : P.Base)
    (i j : b.support) (hij : i ≠ j) (R : Type*) [CommRing R] :
    Commute ((stringsOfWeightOrbit P S hc hm).step R i.val (-1))
      ((stringsOfWeightOrbit P S hc hm).step R j.val 1) := by
  let T := stringsOfWeightOrbit P S hc hm
  have grade (a c : ι) (μ : WeightOrbit P S) :
      T.pairing a (T.reflection c μ) =
        T.pairing a μ - T.pairing c μ * P.pairingIn ℤ c a :=
    weightReflection_other_grade P a c μ.val
  have nonposij : P.pairingIn ℤ i.val j.val ≤ 0 := b.cartanMatrix_le_zero_of_ne i j hij
  have nonposji : P.pairingIn ℤ j.val i.val ≤ 0 := b.cartanMatrix_le_zero_of_ne j i hij.symm
  have zeroiff : P.pairingIn ℤ i.val j.val = 0 ↔ P.pairingIn ℤ j.val i.val = 0 :=
    b.cartanMatrix_apply_eq_zero_iff_symm
  change T.step R i.val (-1) * T.step R j.val 1 = T.step R j.val 1 * T.step R i.val (-1)
  apply Finsupp.lhom_ext
  intro μ r
  change T.step R i.val (-1) (T.step R j.val 1 (Finsupp.single μ r)) =
    T.step R j.val 1 (T.step R i.val (-1) (Finsupp.single μ r))
  by_cases hz : P.pairingIn ℤ i.val j.val = 0
  · have hzr := zeroiff.mp hz
    have hi : T.pairing i.val (T.reflection j.val μ) = T.pairing i.val μ := by
      rw [grade, hzr]; ring
    have hj : T.pairing j.val (T.reflection i.val μ) = T.pairing j.val μ := by
      rw [grade, hz]; ring
    have href : T.reflection i.val (T.reflection j.val μ) =
        T.reflection j.val (T.reflection i.val μ) :=
      Subtype.ext (weightReflections_commute_of_zero P i.val j.val hz hzr μ.val)
    by_cases hmi : T.pairing i.val μ = -1 <;>
      by_cases hmj : T.pairing j.val μ = 1 <;> simp [hmi, hmj, hi, hj, href]
  · have hzr : P.pairingIn ℤ j.val i.val ≠ 0 := mt zeroiff.mpr hz
    have boundi := T.minuscule i.val μ
    have boundj := T.minuscule j.val μ
    have hi (h : T.pairing j.val μ = 1) : T.pairing i.val (T.reflection j.val μ) ≠ -1 := by
      rw [grade, h]
      simp only [one_mul]
      omega
    have hj (h : T.pairing i.val μ = -1) : T.pairing j.val (T.reflection i.val μ) ≠ 1 := by
      rw [grade, h]
      simp only [neg_one_mul, sub_neg_eq_add]
      omega
    by_cases hmi : T.pairing i.val μ = -1 <;>
      by_cases hmj : T.pairing j.val μ = 1 <;> simp [hmi, hmj, hi, hj]

/-- Coefficient matrices inherit the actual operator relation. -/
theorem weightOrbit_opposite_stepMatrices_commute (b : P.Base)
    (i j : b.support) (hij : i ≠ j) (R : Type*) [CommRing R] :
    Commute ((stringsOfWeightOrbit P S hc hm).stepMatrix R i.val (-1))
      ((stringsOfWeightOrbit P S hc hm).stepMatrix R j.val 1) := by
  have he := congrArg (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne)
    (weightOrbit_opposite_steps_commute P S hc hm b i j hij R).eq
  change _ * _ = _ * _
  simpa only [LinearMap.toMatrix_mul, Strings.stepMatrix] using he

/-- Actual invertible root matrices commute for opposite, distinct simple roots. -/
theorem weightOrbit_opposite_rootElements_commute (b : P.Base)
    (i j : b.support) (hij : i ≠ j) (R : Type*) [CommRing R] (s t : R) :
    Commute (weightOrbitRootElement P S hc hm R i.val (-1) (by decide) s)
      (weightOrbitRootElement P S hc hm R j.val 1 (by decide) t) := by
  have h := ((weightOrbit_opposite_stepMatrices_commute P S hc hm b i j hij R).smul_left s).smul_right t
  change _ * _ = _ * _
  apply Units.ext
  change (1 + s • (stringsOfWeightOrbit P S hc hm).stepMatrix R i.val (-1)) *
      (1 + t • (stringsOfWeightOrbit P S hc hm).stepMatrix R j.val 1) =
    (1 + t • (stringsOfWeightOrbit P S hc hm).stepMatrix R j.val 1) *
      (1 + s • (stringsOfWeightOrbit P S hc hm).stepMatrix R i.val (-1))
  exact ((Commute.one_right _).add_right ((Commute.one_left _).add_left h)).eq

end Atlas.Chevalley.Integral.Minuscule
