import Atlas.Rudvalis.FourActiveMatrices

/-! Equality in the bilinear lower bound gives exactly the rank-one stratum. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem affine_base_sum (M : BinaryMatrix) :
    (∑ p : Point, if matrixAt M p.val = 0 then (0 : ℕ) else 4) =
      4 * (nonzeroMatrixBlocks M).card := by
  simp only [nonzeroMatrixBlocks, Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : matrixAt M p.val = 0 <;> simp [hp]

theorem binaryNormalMap_affine_weight (ε : Point → Bit) (M : BinaryMatrix) :
    hammingNorm (binaryNormalMap (ε,M,0)) =
      ∑ p : Point, if matrixAt M p.val=0 then (if ε p=0 then 0 else 8) else 4 := by
  rw [binaryNormalMap_weight]
  apply Finset.sum_congr rfl
  intro p _
  change blockWeight (ε p) (matrixAt M p.val + eta p 0) 0 = _
  have he : eta p 0 = 0 := by simp [eta]
  rw [he,add_zero,blockWeight_affine]

theorem binaryNormalMap_bilinear_weight_sixteen (ε : Point → Bit) (M : BinaryMatrix)
    (hM : M ≠ 0) :
    hammingNorm (binaryNormalMap (ε,M,0)) = 16 ↔
      isBinaryRankOne M ∧ (∀ p : Point, matrixAt M p.val=0 → ε p=0) := by
  classical
  rw [binaryNormalMap_affine_weight]
  have hl : ∀ p ∈ (Finset.univ : Finset Point),
      (if matrixAt M p.val=0 then 0 else 4) ≤
        (if matrixAt M p.val=0 then (if ε p=0 then 0 else 8) else 4 : ℕ) := by
    intro p _; split_ifs <;> omega
  constructor
  · intro hw
    have hle := Finset.sum_le_sum hl
    rw [affine_base_sum,hw] at hle
    have hlo := nonzeroMatrixBlocks_lower M hM
    have hc : (nonzeroMatrixBlocks M).card=4 := by omega
    refine ⟨fourActive_isBinaryRankOne M hM hc, ?_⟩
    have heq := (Finset.sum_eq_sum_iff_of_le hl).mp
      (by rw [affine_base_sum,hc,hw])
    intro p hp
    have he := heq p (Finset.mem_univ p)
    simp only [hp,ite_true] at he
    split_ifs at he with heps
    · exact heps
  · rintro ⟨hRank,hε⟩
    calc
      _ = ∑ p : Point, if matrixAt M p.val=0 then 0 else 4 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : matrixAt M p.val=0
        · simp [hp,hε p hp]
        · simp [hp]
      _ = 16 := by rw [affine_base_sum,(isBinaryRankOne_iff M).mp hRank |>.2]

end Atlas.Rudvalis
