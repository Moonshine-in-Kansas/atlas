import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation
import Atlas.LinearGroups.Chevalley.Integral.MinusculeCrossTorus

/-! Every actual minuscule weight has grade zero at the two nodes of a
triple edge. Thus both actual simple-root matrix families are trivial on
these blocks, integrally and over every commutative coefficient ring. -/

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

include hc hm

theorem weightOrbit_tripleEdge_grades_zero (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3)
    (μ : WeightOrbit P S) :
    μ.val (corootElement P i) = 0 ∧ μ.val (corootElement P j) = 0 := by
  let T := stringsOfWeightOrbit P S hc hm
  have hgradeij (ν : WeightOrbit P S) :
      T.pairing j (T.reflection i ν) = T.pairing j ν + T.pairing i ν := by
    change (weightReflection P i ν.val) (corootElement P j) =
      ν.val (corootElement P j) + ν.val (corootElement P i)
    simpa only [hij, mul_neg_one, sub_neg_eq_add] using
      weightReflection_other_grade P j i ν.val
  have hgradeji (ν : WeightOrbit P S) :
      T.pairing i (T.reflection j ν) = T.pairing i ν + 3 * T.pairing j ν := by
    change (weightReflection P j ν.val) (corootElement P i) =
      ν.val (corootElement P i) + 3 * ν.val (corootElement P j)
    rw [weightReflection_other_grade, hji]
    ring
  have hjzero (ν : WeightOrbit P S) : T.pairing j ν = 0 := by
    have hi := T.minuscule i ν
    have hj := T.minuscule j ν
    have hnext := T.minuscule i (T.reflection j ν)
    rw [hgradeji] at hnext
    omega
  have hizero : T.pairing i μ = 0 := by
    have hnext := hjzero (T.reflection i μ)
    rw [hgradeij, hjzero] at hnext
    omega
  exact ⟨hizero, hjzero μ⟩

variable (R : Type*) [CommRing R]

theorem weightOrbit_tripleEdge_stepMatrix_eq_zero (i j k : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3)
    (hk : k = i ∨ k = j) (ε : ℤ) (hε : ε ≠ 0) :
    (stringsOfWeightOrbit P S hc hm).stepMatrix R k ε = 0 := by
  ext μ ν
  have h := weightOrbit_tripleEdge_grades_zero P S hc hm i j hij hji ν
  have hkzero : ν.val (corootElement P k) = 0 := by
    rcases hk with rfl | rfl
    · exact h.1
    · exact h.2
  simp only [weightOrbit_stepMatrix_entry, hkzero, Ne.symm hε, false_and,
    ite_false, Matrix.zero_apply]

theorem weightOrbit_tripleEdge_rootElement_eq_one (i j k : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3)
    (hk : k = i ∨ k = j) (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    weightOrbitRootElement P S hc hm R k ε hε t = 1 := by
  apply Units.ext
  change 1 + t • (stringsOfWeightOrbit P S hc hm).stepMatrix R k ε = 1
  rw [weightOrbit_tripleEdge_stepMatrix_eq_zero P S hc hm R i j k hij hji hk ε hε,
    smul_zero, add_zero]

theorem weightOrbit_tripleEdge_weylMatrixUnit_eq_one (i j k : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3)
    (hk : k = i ∨ k = j) (a : Rˣ) :
    (stringsOfWeightOrbit P S hc hm).weylMatrixUnit R k a = 1 := by
  change weightOrbitRootElement P S hc hm R k (-1) (by decide) a.val *
    weightOrbitRootElement P S hc hm R k 1 (by decide) (-(a⁻¹).val) *
    weightOrbitRootElement P S hc hm R k (-1) (by decide) a.val = 1
  simp only [weightOrbit_tripleEdge_rootElement_eq_one P S hc hm R i j k hij hji hk,
    one_mul]

end Atlas.Chevalley.Integral.Minuscule
