import Atlas.Rudvalis.QuadraticEnumerator
import Atlas.Rudvalis.MatrixRankCounts

/-! The full residue weight enumerator, assembled from structural fibre counts. -/
namespace Atlas.Rudvalis
open scoped BigOperators
variable {R : Type*} [CommSemiring R]

theorem binaryMatrix_weighted_sum (f : ℕ → R) :
    (∑ M : BinaryMatrix, f (nonzeroMatrixBlocks M).card) =
      f 0 + 49*f 4 + 294*f 6 + 168*f 7 := by
  classical
  have he (M : BinaryMatrix) : f (nonzeroMatrixBlocks M).card =
      (if (nonzeroMatrixBlocks M).card=0 then f 0 else 0) +
      (if (nonzeroMatrixBlocks M).card=4 then f 4 else 0) +
      (if (nonzeroMatrixBlocks M).card=6 then f 6 else 0) +
      (if (nonzeroMatrixBlocks M).card=7 then f 7 else 0) := by
    rcases binaryMatrix_active_sizes M with h | h | h | h <;> simp [h]
  have hcount (k : ℕ) :
      (Finset.univ.filter (fun M : BinaryMatrix => (nonzeroMatrixBlocks M).card=k)).card =
      Nat.card {M : BinaryMatrix // (nonzeroMatrixBlocks M).card=k} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp_rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]
  rw [hcount 0,hcount 4,hcount 6,hcount 7,binaryMatrix_zero_card,binaryMatrix_four_card,
    binaryMatrix_six_card,binaryMatrix_seven_card]
  simp

theorem binaryAffine_weight_sum (z : R) :
    (∑ M : BinaryMatrix, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,0))) =
      (1+z^8)^7 + 49*(2*z^4)^4*(1+z^8)^3 +
      294*(2*z^4)^6*(1+z^8) + 168*(2*z^4)^7 := by
  simp_rw [binaryNormalMap_affine_sum]
  rw [binaryMatrix_weighted_sum (fun k => (2*z^4)^k*(1+z^8)^(7-k))]
  norm_num
  ring

theorem binaryResidue_weight_enumerator (z : R) :
    binaryWeightSum z =
      (1+z^8)^7 + 49*(2*z^4)^4*(1+z^8)^3 +
      294*(2*z^4)^6*(1+z^8) + 168*(2*z^4)^7 +
      448*((2*z^4)*(z^2+z^6)^6 + 4*(2*z^4)^3*(z^2+z^6)^4 +
        3*(2*z^4)^5*(z^2+z^6)^2) := by
  classical
  rw [binaryWeightSum_fibres,
    ← Fintype.sum_subtype_add_sum_subtype (fun c : E => c=0)]
  have hz : (∑ c : {c : E // c=0}, ∑ M : BinaryMatrix, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,c.val))) =
      ∑ M : BinaryMatrix, ∑ ε : Point → Bit,
        z ^ hammingNorm (binaryNormalMap (ε,M,0)) := by
    simp only [Fintype.sum_unique]
    rw [(default : {c : E // c=0}).prop]
  change (∑ c : {c : E // c=0}, ∑ M : BinaryMatrix, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,c.val))) +
    (∑ c : Point, ∑ M : BinaryMatrix, ∑ ε : Point → Bit,
      z ^ hammingNorm (binaryNormalMap (ε,M,c.val))) = _
  rw [hz,binaryAffine_weight_sum]
  have hn := fun c : Point => binaryQuadratic_coset_weight_sum z c.val c.prop
  simp_rw [hn]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num
  ring

end Atlas.Rudvalis
