import Atlas.Rudvalis.MinimumStrata
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Generating functions from independent block constants, without enumerating the code. -/
namespace Atlas.Rudvalis
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

theorem bit_sum_two (f : Bit → R) : (∑ a, f a) = f 0 + f 1 := by
  have hu : (Finset.univ : Finset Bit) = {0,1} := by decide
  rw [hu]
  simp

def localWeightSum (z : R) (b c : E) : R := ∑ a : Bit, z ^ blockWeight a b c

theorem localWeightSum_affine (z : R) (b : E) :
    localWeightSum z b 0 = if b=0 then 1+z^8 else 2*z^4 := by
  rw [localWeightSum,bit_sum_two]
  simp only [blockWeight_affine]
  by_cases hb : b=0 <;> simp [hb,two_mul]

theorem localWeightSum_quadratic (z : R) (b c : E) (hc : c ≠ 0) :
    localWeightSum z b c =
      if quadratic c c + dot b c=1 then 2*z^4 else z^2+z^6 := by
  rw [localWeightSum,bit_sum_two]
  have h0 := blockWeight_quadratic 0 b c hc
  have h1 := blockWeight_quadratic 1 b c hc
  by_cases hb : quadratic c c + dot b c=1
  · simp only [hb,ite_true] at h0 h1 ⊢
    rw [h0,h1,two_mul]
  · simp only [hb,ite_false] at h0 h1 ⊢
    have hs := blockWeight_complement 0 b c
    simp only [zero_add] at hs
    rcases h0 with h0 | h0
    · have he : blockWeight 1 b c=6 := by omega
      rw [h0,he]
    · have he : blockWeight 1 b c=2 := by omega
      rw [h0,he,add_comm]

theorem binaryNormalMap_constant_sum (z : R) (M : BinaryMatrix) (c : E) :
    (∑ ε : Point → Bit, z ^ hammingNorm (binaryNormalMap (ε,M,c))) =
      ∏ p : Point, localWeightSum z (matrixAt M p.val + eta p c) c := by
  classical
  simp_rw [binaryNormalMap_weight,← Finset.prod_pow_eq_pow_sum]
  exact (Fintype.prod_sum (fun p a => z ^ blockWeight a (matrixAt M p.val + eta p c) c)).symm

theorem seven_factor_product (s : Finset Point) (a b : R) :
    (∏ p : Point, if p ∈ s then a else b) = a^s.card*b^(7-s.card) := by
  classical
  rw [Finset.prod_ite]
  have h : Finset.univ.filter (fun p : Point => p ∉ s) = sᶜ := by ext p; simp
  simp [h,Finset.card_compl]

noncomputable def binaryNormalEquiv : BinaryParameters ≃ binaryResidue :=
  Equiv.ofBijective (fun a => ⟨binaryNormalMap a,⟨a,rfl⟩⟩) (by
    constructor
    · intro a b h
      exact binaryNormalMap_injective (congrArg Subtype.val h)
    · rintro ⟨w,a,rfl⟩
      exact ⟨a,rfl⟩)

noncomputable def binaryWeightSum (z : R) : R := by
  classical
  exact ∑ w : binaryResidue, z ^ hammingNorm w.val

theorem binaryWeightSum_parameters (z : R) :
    binaryWeightSum z = ∑ a : BinaryParameters, z ^ hammingNorm (binaryNormalMap a) := by
  classical
  exact (Equiv.sum_comp binaryNormalEquiv (fun w => z ^ hammingNorm w.val)).symm

theorem binaryNormalMap_affine_sum (z : R) (M : BinaryMatrix) :
    (∑ ε : Point → Bit, z ^ hammingNorm (binaryNormalMap (ε,M,0))) =
      (2*z^4)^(nonzeroMatrixBlocks M).card * (1+z^8)^(7-(nonzeroMatrixBlocks M).card) := by
  classical
  rw [binaryNormalMap_constant_sum,← seven_factor_product]
  apply Finset.prod_congr rfl
  intro p _
  have hz : eta p 0=0 := by simp [eta]
  rw [hz,add_zero,localWeightSum_affine]
  simp only [nonzeroMatrixBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all

theorem binaryNormalMap_quadratic_sum (z : R) (M : BinaryMatrix) (c : E) (hc : c ≠ 0) :
    (∑ ε : Point → Bit, z ^ hammingNorm (binaryNormalMap (ε,M,c))) =
      (2*z^4)^(balancedBlocks c (matrixAt M.transpose c)).card *
      (z^2+z^6)^(7-(balancedBlocks c (matrixAt M.transpose c)).card) := by
  classical
  rw [binaryNormalMap_constant_sum,← seven_factor_product]
  apply Finset.prod_congr rfl
  intro p _
  rw [localWeightSum_quadratic _ _ _ hc,binary_balance_mask]
  simp only [balancedBlocks,Finset.mem_filter,Finset.mem_univ,true_and]

end Atlas.Rudvalis
