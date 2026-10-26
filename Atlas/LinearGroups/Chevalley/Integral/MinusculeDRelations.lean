import Atlas.LinearGroups.Chevalley.Integral.MinusculeDSpan
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Integral relations in the actual D weight/root quotient.
No quotient cardinality or abstract center identification is assumed. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

/-- The plus root supplies the complementary relation to the minus root. -/
theorem rootWeight_sum {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    rootWeight (pairingD r) (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl)) =
      coordinateWeight i + coordinateWeight j := by
  ext x
  change x.val (Pi.single i 1 + Pi.single j 1) =
    x.val (Pi.single i 1) + x.val (Pi.single j 1)
  exact map_add _ _ _

theorem coordinate_difference_mem (n : ℕ) (i j : Fin (n+2)) :
    coordinateWeight i - coordinateWeight j ∈ rootLattice (pairingD (n+2)) := by
  by_cases hij : i=j
  · subst j
    simp
  · rw [← rootWeight_difference i j hij]
    exact rootWeight_mem_rootLattice _ _

/-- Twice any coordinate weight is explicitly a sum of two actual roots. -/
theorem twice_coordinate_mem (n : ℕ) (i : Fin (n+2)) :
    (2 : ℤ) • coordinateWeight i ∈ rootLattice (pairingD (n+2)) := by
  obtain ⟨j,hji⟩ := exists_ne i
  have h₁ := rootWeight_mem_rootLattice (pairingD (n+2))
    (longRoot false i j (Ne.symm hji) 1 1 (Or.inl rfl) (Or.inl rfl))
  have h₂ := coordinate_difference_mem n i j
  rw [rootWeight_sum] at h₁
  have h := (rootLattice (pairingD (n+2))).add_mem h₁ h₂
  convert h using 1 <;> module

/-- The doubled positive spin weight has the literal coordinate-sum expression. -/
theorem twice_positive_spinWeight (n : ℕ) :
    (2 : ℤ) • spinWeight n (fun _ => true) = ∑ k, coordinateWeight (r := n+2) k := by
  ext x
  have h := twice_spinWeight_apply n (fun _ => true) x
  simpa [sign, coordinateWeight, LinearMap.sum_apply] using h

abbrev WeightRootQuotient (n : ℕ) :=
  WeightLattice (pairingD (n+2)) ⧸ rootLattice (pairingD (n+2))

def weightClass (n : ℕ) : WeightLattice (pairingD (n+2)) →ₗ[ℤ] WeightRootQuotient n :=
  (rootLattice (pairingD (n+2))).mkQ

theorem weightClass_zero_iff (n : ℕ) (μ : WeightLattice (pairingD (n+2))) :
    weightClass n μ = 0 ↔ μ ∈ rootLattice (pairingD (n+2)) := by
  change (Submodule.Quotient.mk μ : WeightRootQuotient n) = Submodule.Quotient.mk 0 ↔ _
  rw [Submodule.Quotient.eq, sub_zero]

theorem coordinate_classes_equal (n : ℕ) (i j : Fin (n+2)) :
    weightClass n (coordinateWeight i) = weightClass n (coordinateWeight j) := by
  apply sub_eq_zero.mp
  rw [← map_sub, weightClass_zero_iff]
  exact coordinate_difference_mem n i j

def vectorClass (n : ℕ) : WeightRootQuotient n :=
  weightClass n (coordinateWeight (Fin.last (n+1)))

def positiveSpinClass (n : ℕ) : WeightRootQuotient n :=
  weightClass n (spinWeight n (fun _ => true))

def negativeSpinClass (n : ℕ) : WeightRootQuotient n :=
  weightClass n (spinWeight n (lastNegative n))

theorem twice_vectorClass (n : ℕ) : (2 : ℤ) • vectorClass n = 0 := by
  rw [vectorClass, ← map_smul, weightClass_zero_iff]
  exact twice_coordinate_mem n _

theorem spin_class_difference (n : ℕ) :
    positiveSpinClass n - negativeSpinClass n = vectorClass n := by
  unfold positiveSpinClass negativeSpinClass vectorClass
  rw [← map_sub, selected_difference]

/-- Uniform rank-sensitive relation; it determines the odd/even distinction. -/
theorem twice_positiveSpinClass (n : ℕ) :
    (2 : ℤ) • positiveSpinClass n = (n+2 : ℤ) • vectorClass n := by
  unfold positiveSpinClass
  rw [← map_smul, twice_positive_spinWeight, map_sum]
  have he : ∀ k : Fin (n+2), weightClass n (coordinateWeight k) = vectorClass n :=
    fun k => coordinate_classes_equal n k (Fin.last (n+1))
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_cast

/-- All ranks have the exponent-four relation without using a determinant. -/
theorem four_positiveSpinClass (n : ℕ) : (4 : ℤ) • positiveSpinClass n = 0 := by
  calc
    (4 : ℤ) • positiveSpinClass n = (2 : ℤ) • ((2 : ℤ) • positiveSpinClass n) := by
      rw [smul_smul]; norm_num
    _ = (2 : ℤ) • ((n+2 : ℤ) • vectorClass n) := by rw [twice_positiveSpinClass]
    _ = (n+2 : ℤ) • ((2 : ℤ) • vectorClass n) := by rw [smul_comm]
    _ = 0 := by rw [twice_vectorClass, smul_zero]

/-- At even rank the positive half-spin class is killed by two. -/
theorem even_rank_twice_positiveSpinClass (n : ℕ) (h : Even (n+2)) :
    (2 : ℤ) • positiveSpinClass n = 0 := by
  obtain ⟨k,hk⟩ := h
  rw [twice_positiveSpinClass]
  have hc : (n+2 : ℤ) = (k : ℤ)*2 := by
    have hn : n+2 = k*2 := by omega
    exact_mod_cast hn
  rw [hc, mul_smul, twice_vectorClass, smul_zero]

/-- At odd rank the vector class is twice the positive spin class. -/
theorem odd_rank_vectorClass (n : ℕ) (h : Odd (n+2)) :
    vectorClass n = (2 : ℤ) • positiveSpinClass n := by
  obtain ⟨k,hk⟩ := h
  rw [twice_positiveSpinClass]
  have hc : (n+2 : ℤ) = (k : ℤ)*2+1 := by
    have hn : n+2 = k*2+1 := by omega
    exact_mod_cast hn
  rw [hc, add_smul, mul_smul, twice_vectorClass, smul_zero, one_smul, zero_add]

end Atlas.Chevalley.Integral.Minuscule.TypeD
