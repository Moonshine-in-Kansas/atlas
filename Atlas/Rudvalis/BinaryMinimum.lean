import Atlas.Rudvalis.BalanceMasks
import Atlas.Rudvalis.BinaryRestriction

/-! Structural lower bounds and the weight-eight residue words. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def nonzeroMatrixBlocks (M : Matrix (Fin 3) (Fin 3) Bit) : Finset Point :=
  Finset.univ.filter (fun p => matrixAt M p.val ≠ 0)

theorem linear_ones_count (b : E) (hb : b ≠ 0) :
    (Finset.univ.filter (fun p : Point => dot b p.val = 1)).card = 4 := by
  decide +kernel +revert

theorem nonzeroMatrixBlocks_lower (M : Matrix (Fin 3) (Fin 3) Bit) (hM : M ≠ 0) :
    4 ≤ (nonzeroMatrixBlocks M).card := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, M j ≠ 0 := Function.ne_iff.mp hM
  rw [← linear_ones_count (M j) hj]
  apply Finset.card_le_card
  intro p hp
  simp only [nonzeroMatrixBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  intro hz
  have hh := congrFun hz j
  change dot (M j) p.val = 0 at hh
  rw [hp] at hh
  exact one_ne_zero hh

theorem binaryNormalMap_affine_lower (a : BinaryParameters)
    (hc : a.2.2 = 0) (hM : a.2.1 ≠ 0) : 16 ≤ hammingNorm (binaryNormalMap a) := by
  classical
  have hz (p : Point) : eta p 0 = 0 := by simp [eta]
  have hs : (∑ p : Point, if matrixAt a.2.1 p.val = 0 then (0 : ℕ) else 4) =
      4 * (nonzeroMatrixBlocks a.2.1).card := by
    simp only [nonzeroMatrixBlocks, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : matrixAt a.2.1 p.val = 0 <;> simp [hp]
  rw [binaryNormalMap_weight]
  calc
    16 ≤ 4 * (nonzeroMatrixBlocks a.2.1).card := by
      have := nonzeroMatrixBlocks_lower a.2.1 hM
      omega
    _ = ∑ p : Point, if matrixAt a.2.1 p.val = 0 then 0 else 4 := hs.symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      rw [hc, hz, add_zero, blockWeight_affine]
      split_ifs <;> omega

theorem binaryNormalMap_constant_weight (ε : Point → Bit) :
    hammingNorm (binaryNormalMap (ε,0,0)) = 8 * hammingNorm ε := by
  have hm (p : E) : matrixAt (0 : Matrix (Fin 3) (Fin 3) Bit) p = 0 := by
    ext j
    simp [matrixAt]
  have he (p : Point) : eta p 0 = 0 := by simp [eta]
  rw [binaryNormalMap_weight, Atlas.Codes.hammingNorm_eq_sum]
  change (∑ p : Point, blockWeight (ε p) (matrixAt 0 p.val + eta p 0) 0) = _
  simp only [hm, he, add_zero, blockWeight_affine, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ε p = 0 <;> simp [hp]

/-- Below sixteen, the normal form must be purely constant on each row. -/
theorem binaryNormalMap_small_parameters (a : BinaryParameters)
    (hw : hammingNorm (binaryNormalMap a) < 16) : a.2.1 = 0 ∧ a.2.2 = 0 := by
  have hc : a.2.2 = 0 := by
    by_contra hc
    have := binaryNormalMap_quadratic_lower a hc
    omega
  refine ⟨?_,hc⟩
  by_contra hm
  have := binaryNormalMap_affine_lower a hc hm
  omega

/-- The minimum nonzero residue weight is at least eight. -/
theorem binaryResidue_minimum (w : BinaryWord) (hw : w ∈ binaryResidue) (hne : w ≠ 0) :
    8 ≤ hammingNorm w := by
  obtain ⟨a,rfl⟩ := hw
  by_cases hsmall : hammingNorm (binaryNormalMap a) < 16
  · obtain ⟨hM,hc⟩ := binaryNormalMap_small_parameters a hsmall
    have ha : a = (a.1,0,0) := Prod.ext rfl (Prod.ext hM hc)
    rw [ha, binaryNormalMap_constant_weight]
    have he : a.1 ≠ 0 := by
      intro hzero
      apply hne
      rw [ha,hzero]
      exact map_zero binaryNormalMap
    have hwpos : 0 < hammingNorm a.1 := Nat.pos_of_ne_zero (hammingNorm_eq_zero.not.mpr he)
    omega
  · omega

end Atlas.Rudvalis
