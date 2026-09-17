import Atlas.Algebra.BinaryQuadraticNormalization
import Atlas.Algebra.BinaryWalshRank
import Atlas.Codes.BinaryWeight
import Mathlib.Tactic.IntervalCases

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

theorem binaryWalshSign_sum_weight {ι : Type*} [Fintype ι] (w : ι → Bit) :
    ∑ i, binaryWalshSign (w i) = (Fintype.card ι : ℤ)-2*hammingNorm w := by
  classical
  have hb : ∀ b : Bit, binaryWalshSign b = 1-2*(if b=0 then (0 : ℕ) else 1 : ℤ) := by decide
  simp only [hb,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,← Finset.mul_sum]
  have hh : (∑ i, if w i=0 then (0 : ℤ) else 1)=(hammingNorm w : ℤ) := by
    rw [hammingNorm_eq_sum,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  simpa only [Nat.cast_zero] using congrArg (fun z : ℤ => (Fintype.card ι : ℤ)-2*z) hh

theorem binaryQuadraticWordForm_walsh_square (w : binaryQuadraticCode) :
    binaryWalsh (binaryQuadraticWordForm w) 0 ^ 2 = (16-2*(hammingNorm w.val : ℤ))^2 := by
  have h : binaryWalsh (binaryQuadraticWordForm w) 0 =
      (∑ v, binaryWalshSign (w.val v))*binaryWalshSign (w.val 0) := by
    simp only [binaryWalsh,AddMonoidHom.zero_apply,add_zero,binaryQuadraticWordForm_apply,
      binaryWalshSign_add,Finset.sum_mul]
  rw [h,mul_pow,binaryWalshSign_sq,mul_one,binaryWalshSign_sum_weight]
  have hc : Fintype.card BinaryFour=16 := by decide
  rw [hc]
  norm_num

/-- Recover polar rank from one nonzero Walsh coefficient, using the actual
radical and the previously proved Walsh-square identity. -/
theorem binaryFourPolarRank_of_walsh_square (q : QuadraticMap Bit BinaryFour Bit) (r : ℕ)
    (hr : r=2 ∨ r=4) (hw : binaryWalsh q 0 ^ 2=16*2^(4-r)) : binaryWalshPolarRank q=r := by
  have hd : Module.finrank Bit BinaryFour=4 := by simp [BinaryFour]
  have hn := q.polarBilin.finrank_range_add_finrank_ker
  rw [hd] at hn
  change binaryWalshPolarRank q+Module.finrank Bit q.polarBilin.ker=4 at hn
  have hbound : binaryWalshPolarRank q ≤ 4 := by omega
  have hcompat : BinaryWalshCompatible q 0 := by
    by_contra h
    have hz := binaryWalsh_eq_zero_of_not_compatible q 0 h
    rw [hz] at hw
    rcases hr with rfl | rfl <;> norm_num at hw
  have hs := binaryWalsh_sq_of_compatible q 0 hcompat
  rw [binaryWalshRadical_card] at hs
  have hc : Fintype.card BinaryFour=16 := by decide
  rw [hc,hd,hw] at hs
  generalize hk : binaryWalshPolarRank q=k at hs hbound ⊢
  rcases hr with rfl | rfl <;> interval_cases k <;> norm_num at hs <;> norm_num

theorem binaryQuadraticWordForm_rank_four_of_weight_six (w : binaryQuadraticCode)
    (hw : hammingNorm w.val=6) : binaryWalshPolarRank (binaryQuadraticWordForm w)=4 := by
  apply binaryFourPolarRank_of_walsh_square _ 4 (Or.inr rfl)
  rw [binaryQuadraticWordForm_walsh_square,hw]
  norm_num

theorem binaryQuadraticWordForm_rank_two_of_weight_four (w : binaryQuadraticCode)
    (hw : hammingNorm w.val=4) : binaryWalshPolarRank (binaryQuadraticWordForm w)=2 := by
  apply binaryFourPolarRank_of_walsh_square _ 2 (Or.inl rfl)
  rw [binaryQuadraticWordForm_walsh_square,hw]
  norm_num

end Atlas.Algebra
