import Atlas.LinearGroups.Chevalley.Integral.MinusculeDRelations
import Mathlib.Data.ZMod.Basic

/-! explicit characters of P/Q for D, built from actual coroots. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

/-- A genuine coroot-lattice element with ambient value twice the ith coordinate. -/
def coordinateTest (n : ℕ) (i : Fin (n+2)) : CorootLattice (pairingD (n+2)) :=
  doubleCoordinate n i (Classical.choose (exists_ne i))
    (Ne.symm (Classical.choose_spec (exists_ne i)))

theorem coordinateTest_apply (n : ℕ) (i : Fin (n+2)) (x : ClassicalData.Lattice (n+2)) :
    (coordinateTest n i).val x = 2*x i := by
  unfold coordinateTest doubleCoordinate
  change coroot (longRoot false i _ _ 1 1 _ _) x +
    coroot (longRoot false i _ _ 1 (-1) _ _) x = _
  rw [coroot_long,coroot_long]
  ring

theorem spinWeight_coordinateTest (n : ℕ) (σ : Fin (n+2) → Bool) (i : Fin (n+2)) :
    spinWeight n σ (coordinateTest n i) = sign (σ i) :=
  spinWeight_doubleCoordinate n σ i _ _

/-- The parity of a doubled coordinate detects whether a weight is half-integral. -/
def spinParityCharacter (n : ℕ) : WeightLattice (pairingD (n+2)) →ₗ[ℤ] ZMod 2 where
  toFun μ := (μ (coordinateTest n 0) : ZMod 2)
  map_add' μ ν := by simp
  map_smul' t μ := by simp [Int.cast_mul]

/-- Twice the total coordinate sum, modulo four; no division or determinant. -/
def totalCharacter (n : ℕ) : WeightLattice (pairingD (n+2)) →ₗ[ℤ] ZMod 4 where
  toFun μ := ((∑ i, μ (coordinateTest n i) : ℤ) : ZMod 4)
  map_add' μ ν := by simp [Finset.sum_add_distrib]
  map_smul' t μ := by simp [Finset.mul_sum,Int.cast_mul]

theorem spinParityCharacter_root (n : ℕ) (a : DRoot (n+2)) :
    spinParityCharacter n (rootWeight (pairingD (n+2)) a) = 0 := by
  change (((coordinateTest n 0).val a.val : ℤ) : ZMod 2) = 0
  rw [coordinateTest_apply]
  simp [show (2 : ZMod 2) = 0 by decide]

theorem totalCharacter_root (n : ℕ) (a : DRoot (n+2)) :
    totalCharacter n (rootWeight (pairingD (n+2)) a) = 0 := by
  change ((∑ i, (coordinateTest n i).val a.val : ℤ) : ZMod 4) = 0
  simp only [coordinateTest_apply]
  rcases signed_support_classification a with ⟨h,_⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · cases h
  · rw [ha]
    simp only [Pi.add_apply,Pi.single_apply,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num <;> decide

theorem rootLattice_le_spinParityKernel (n : ℕ) :
    rootLattice (pairingD (n+2)) ≤ LinearMap.ker (spinParityCharacter n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact spinParityCharacter_root n a

theorem rootLattice_le_totalKernel (n : ℕ) :
    rootLattice (pairingD (n+2)) ≤ LinearMap.ker (totalCharacter n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact totalCharacter_root n a

def quotientSpinParity (n : ℕ) : WeightRootQuotient n →ₗ[ℤ] ZMod 2 :=
  (rootLattice (pairingD (n+2))).liftQ (spinParityCharacter n) (rootLattice_le_spinParityKernel n)

def quotientTotal (n : ℕ) : WeightRootQuotient n →ₗ[ℤ] ZMod 4 :=
  (rootLattice (pairingD (n+2))).liftQ (totalCharacter n) (rootLattice_le_totalKernel n)

theorem quotientSpinParity_positive (n : ℕ) :
    quotientSpinParity n (positiveSpinClass n) = 1 := by
  change ((spinWeight n (fun _ => true) (coordinateTest n 0) : ℤ) : ZMod 2) = 1
  rw [spinWeight_coordinateTest]
  rfl

theorem quotientSpinParity_vector (n : ℕ) : quotientSpinParity n (vectorClass n) = 0 := by
  change (((coordinateTest n 0).val (Pi.single (Fin.last (n+1)) 1) : ℤ) : ZMod 2) = 0
  rw [coordinateTest_apply]
  simp

theorem quotientTotal_positive (n : ℕ) :
    quotientTotal n (positiveSpinClass n) = (n+2 : ZMod 4) := by
  change ((∑ i, spinWeight n (fun _ => true) (coordinateTest n i) : ℤ) : ZMod 4) = _
  simp [spinWeight_coordinateTest,sign]

theorem quotientTotal_vector (n : ℕ) : quotientTotal n (vectorClass n) = 2 := by
  change ((∑ i, (coordinateTest n i).val (Pi.single (Fin.last (n+1)) 1) : ℤ) : ZMod 4) = 2
  simp [coordinateTest_apply,Pi.single_apply,mul_ite]

/-- In particular, the vector class never collapses, including rank two. -/
theorem vectorClass_ne_zero (n : ℕ) : vectorClass n ≠ 0 := by
  intro h
  have he := quotientTotal_vector n
  rw [h,map_zero] at he
  exact (show (0 : ZMod 4) ≠ 2 by decide) he

theorem positiveSpinClass_ne_zero (n : ℕ) : positiveSpinClass n ≠ 0 := by
  intro h
  have he := quotientSpinParity_positive n
  rw [h,map_zero] at he
  exact zero_ne_one he

end Atlas.Chevalley.Integral.Minuscule.TypeD
