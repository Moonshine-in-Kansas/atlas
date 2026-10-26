import Atlas.Rudvalis.WeightEnumerator

/-! The quadratic contribution to the full residue weight enumerator. -/
namespace Atlas.Rudvalis
open scoped BigOperators
variable {R : Type*} [CommSemiring R]

theorem transposeContraction_sum (c : E) (hc : c ≠ 0) (f : E → R) :
    (∑ M : BinaryMatrix, f (matrixAt M.transpose c)) = 64 * ∑ b : E, f b := by
  classical
  rw [← Fintype.sum_fiberwise' (fun M : BinaryMatrix => matrixAt M.transpose c) f]
  simp only [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,
    transposeContraction_fibre_card c hc,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  norm_num

theorem balancedBlocks_weighted_sum (c : E) (hc : c ≠ 0) (f : ℕ → R) :
    (∑ b : E, f (balancedBlocks c b).card) = f 1 + 4*f 3 + 3*f 5 := by
  classical
  obtain ⟨h1,h3,h5⟩ := balancedBlocks_distribution c hc
  have he (b : E) : f (balancedBlocks c b).card =
      (if (balancedBlocks c b).card=1 then f 1 else 0) +
      (if (balancedBlocks c b).card=3 then f 3 else 0) +
      (if (balancedBlocks c b).card=5 then f 5 else 0) := by
    rcases balancedBlocks_sizes c b hc with h | h | h <;> simp [h]
  simp_rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]
  rw [h1,h3,h5]
  simp

theorem binaryQuadratic_coset_weight_sum (z : R) (c : E) (hc : c ≠ 0) :
    (∑ M : BinaryMatrix, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,c))) =
      64*((2*z^4)*(z^2+z^6)^6 + 4*(2*z^4)^3*(z^2+z^6)^4 +
        3*(2*z^4)^5*(z^2+z^6)^2) := by
  simp_rw [binaryNormalMap_quadratic_sum z _ c hc]
  rw [transposeContraction_sum c hc
      (fun b => (2*z^4)^(balancedBlocks c b).card * (z^2+z^6)^(7-(balancedBlocks c b).card)),
    balancedBlocks_weighted_sum c hc (fun k => (2*z^4)^k*(z^2+z^6)^(7-k))]
  simp only [pow_one]
  norm_num
  simp only [mul_assoc]

theorem binaryWeightSum_fibres (z : R) :
    binaryWeightSum z = ∑ c : E, ∑ M : BinaryMatrix, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,c)) := by
  rw [binaryWeightSum_parameters]
  simp only [Fintype.sum_prod_type]
  trans ∑ M : BinaryMatrix, ∑ c : E, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,c))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro M _
    exact Finset.sum_comm
  · exact Finset.sum_comm

end Atlas.Rudvalis
