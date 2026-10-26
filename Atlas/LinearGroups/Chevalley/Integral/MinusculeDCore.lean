import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesD
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice
import Mathlib.Tactic

/-! actual integral D half-spin weights. Orbit parity and
transitivity are deliberately outside this first checkpoint. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

def sign (b : Bool) : ℤ := if b then 1 else -1

def halfDifference (a b : Bool) : ℤ :=
  if a then (if b then 0 else 1) else (if b then -1 else 0)

def halfSum (a b : Bool) : ℤ :=
  if a then (if b then 1 else 0) else (if b then 0 else -1)

theorem twice_halfDifference (a b : Bool) :
    2 * halfDifference a b = sign a - sign b := by
  cases a <;> cases b <;> decide

theorem twice_halfSum (a b : Bool) :
    2 * halfSum a b = sign a + sign b := by
  cases a <;> cases b <;> decide

/-- The checked D numbering has a final sum root and all earlier difference roots. -/
def spinCoordinates (n : ℕ) (σ : Fin (n+2) → Bool) (i : Fin (n+2)) : ℤ :=
  if h : i.val=n+1 then halfSum (σ ⟨n,by omega⟩) (σ ⟨n+1,by omega⟩)
  else halfDifference (σ i) (σ ⟨i.val+1,by omega⟩)

/-- The spin weight is an actual integral functional on the constructed D coroot lattice. -/
def spinWeight (n : ℕ) (σ : Fin (n+2) → Bool) : WeightLattice (pairingD (n+2)) :=
  (weightCoordinates (pairingD (n+2)) (baseD n)).symm
    (fun j => spinCoordinates n σ ((baseDIndexEquiv n).symm j))

theorem spinWeight_coordinates (n : ℕ) (σ : Fin (n+2) → Bool) (i : Fin (n+2)) :
    weightCoordinates (pairingD (n+2)) (baseD n) (spinWeight n σ)
      (baseDIndexEquiv n i) = spinCoordinates n σ i := by
  simp only [spinWeight, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Literal signed coordinate evaluation restricted to the actual D coroot span. -/
def signedEvaluation (n : ℕ) (σ : Fin (n+2) → Bool) : WeightLattice (pairingD (n+2)) where
  toFun x := ∑ k, sign (σ k) * x.val (Pi.single k 1)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.mul_sum, mul_left_comm]

theorem signedEvaluation_coordinates (n : ℕ) (σ : Fin (n+2) → Bool) (i : Fin (n+2)) :
    weightCoordinates (pairingD (n+2)) (baseD n) (signedEvaluation n σ)
      (baseDIndexEquiv n i) = 2 * spinCoordinates n σ i := by
  rw [weightCoordinates_apply]
  have hb : corootBasis (pairingD (n+2)) (baseD n) (baseDIndexEquiv n i) =
      corootElement (pairingD (n+2)) (simpleD n i) := by
    apply Subtype.ext
    exact (baseD n).flip.coe_toWeightBasisInt_apply
      (⟨simpleD n i, (baseDIndexEquiv n i).property⟩ : (baseD n).flip.support)
  rw [hb]
  change (∑ k, sign (σ k) * coroot (simpleD n i) (Pi.single k 1)) = _
  simp only [simpleD_coroot, functional_apply, dot_single, mul_one, simpleD_vector]
  unfold spinCoordinates
  by_cases hi : i.val=n+1
  · simp [hi, Pi.add_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, twice_halfSum]
  · simp [hi, Pi.sub_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib, twice_halfDifference]

/-- Integral doubled-evaluation identity, valid on all of Q∨. -/
theorem twice_spinWeight (n : ℕ) (σ : Fin (n+2) → Bool) :
    (2 : ℤ) • spinWeight n σ = signedEvaluation n σ := by
  apply (weightCoordinates (pairingD (n+2)) (baseD n)).injective
  funext j
  obtain ⟨i,rfl⟩ := (baseDIndexEquiv n).surjective j
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, spinWeight_coordinates,
    signedEvaluation_coordinates]

theorem twice_spinWeight_apply (n : ℕ) (σ : Fin (n+2) → Bool)
    (x : CorootLattice (pairingD (n+2))) :
    2 * spinWeight n σ x = ∑ k, sign (σ k) * x.val (Pi.single k 1) :=
  congrArg (fun f : WeightLattice (pairingD (n+2)) => f x) (twice_spinWeight n σ)

/-- The second selected sign pattern differs only at the final coordinate. -/
def lastNegative (n : ℕ) (k : Fin (n+2)) : Bool := decide (k.val ≠ n+1)

theorem positive_coordinates (n : ℕ) (i : Fin (n+2)) :
    spinCoordinates n (fun _ => true) i = if i = Fin.last (n+1) then 1 else 0 := by
  by_cases h : i.val=n+1
  · have hi : i=Fin.last (n+1) := Fin.ext h
    simp [spinCoordinates, halfSum, hi]
  · have hi : i≠Fin.last (n+1) := by intro hi; exact h (congrArg Fin.val hi)
    simp [spinCoordinates, h, halfDifference, hi]

theorem lastNegative_coordinates (n : ℕ) (i : Fin (n+2)) :
    spinCoordinates n (lastNegative n) i = if i=(⟨n,by omega⟩ : Fin (n+2)) then 1 else 0 := by
  unfold spinCoordinates
  by_cases hi : i.val=n+1
  · simp [hi, lastNegative, halfSum, Fin.ext_iff]
  · simp [hi, lastNegative, halfDifference]
    all_goals simp only [Fin.ext_iff]

/-- The positive half-spin weight is the actual final fundamental weight. -/
theorem positive_spinWeight (n : ℕ) :
    spinWeight n (fun _ => true) =
      fundamentalWeights (pairingD (n+2)) (baseD n) (baseDIndexEquiv n (Fin.last (n+1))) := by
  apply (weightCoordinates (pairingD (n+2)) (baseD n)).injective
  funext j
  obtain ⟨i,rfl⟩ := (baseDIndexEquiv n).surjective j
  rw [spinWeight_coordinates, positive_coordinates, weightCoordinates_apply, fundamentalWeights_pairing]
  simp

/-- The other chosen half-spin weight is the actual penultimate fundamental weight. -/
theorem negative_spinWeight (n : ℕ) :
    spinWeight n (lastNegative n) =
      fundamentalWeights (pairingD (n+2)) (baseD n) (baseDIndexEquiv n ⟨n,by omega⟩) := by
  apply (weightCoordinates (pairingD (n+2)) (baseD n)).injective
  funext j
  obtain ⟨i,rfl⟩ := (baseDIndexEquiv n).surjective j
  rw [spinWeight_coordinates, lastNegative_coordinates, weightCoordinates_apply, fundamentalWeights_pairing]
  simp

end Atlas.Chevalley.Integral.Minuscule.TypeD
