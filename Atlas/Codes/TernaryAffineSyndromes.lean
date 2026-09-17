import Atlas.Codes.TernaryGolayQuotient
import Atlas.Mathieu.TernaryMathieu11Full
import Mathlib.LinearAlgebra.Dimension.Finite

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def ternaryWordSum : TernaryWord →ₗ[ZMod 3] ZMod 3 where
  toFun w := ∑ i, w i
  map_add' u v := Finset.sum_add_distrib
  map_smul' a w := by simp [Finset.mul_sum]

theorem ternaryGolay_sum_zero (w : TernaryWord) (hw : w ∈ ternaryGolay) :
    ternaryWordSum w = 0 := by
  have h := ternaryGolay_selfOrthogonal hw (fun _ => (1 : ZMod 3)) ternaryGolay_one
  simpa [ternaryWordSum, ternaryDot, dotProductBilin, dotProduct] using h

/-- Syndromes of the actual ternary code. -/
abbrev TernarySyndrome := TernaryWord ⧸ ternaryGolay

def ternarySyndromeClass : TernaryWord →ₗ[ZMod 3] TernarySyndrome := ternaryGolay.mkQ

def ternarySyndromeSum : TernarySyndrome →ₗ[ZMod 3] ZMod 3 :=
  ternaryGolay.liftQ ternaryWordSum ternaryGolay_sum_zero

@[simp] theorem ternarySyndromeSum_class (w : TernaryWord) :
    ternarySyndromeSum (ternarySyndromeClass w) = ternaryWordSum w := rfl

theorem ternarySyndrome_finrank : Module.finrank (ZMod 3) TernarySyndrome = 6 := by
  have h := ternaryGolay.finrank_quotient_add_finrank
  rw [ternaryGolay_finrank] at h
  have hw : Module.finrank (ZMod 3) TernaryWord = 12 := by simp [Module.finrank_pi_fintype]
  rw [hw] at h
  exact Nat.add_right_cancel (h.trans (by decide : 12 = 6+6))

def ternarySyndromeBase : TernarySyndrome := ternarySyndromeClass (Pi.single 0 1)

@[simp] theorem ternarySyndromeBase_sum : ternarySyndromeSum ternarySyndromeBase = 1 := by
  simp [ternarySyndromeBase, ternaryWordSum]

theorem ternarySyndromeSum_surjective : Function.Surjective ternarySyndromeSum := by
  intro a
  refine ⟨a • ternarySyndromeBase, ?_⟩
  simp

theorem ternarySyndromeSum_ker_finrank :
    Module.finrank (ZMod 3) ternarySyndromeSum.ker = 5 := by
  have h := ternarySyndromeSum.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr ternarySyndromeSum_surjective,
    finrank_top, Module.finrank_self, ternarySyndrome_finrank] at h
  exact Nat.add_left_cancel (h.trans (by decide : 6 = 1+5))

/-- The affine sum-one slice of actual code syndromes. -/
def TernaryAffineSyndrome := {s : TernarySyndrome // ternarySyndromeSum s = 1}

def ternaryAffineSyndromeEquiv : ternarySyndromeSum.ker ≃ TernaryAffineSyndrome where
  toFun s := ⟨s.val + ternarySyndromeBase, by simp [s.property]⟩
  invFun s := ⟨s.val - ternarySyndromeBase, by simp [s.property]⟩
  left_inv s := Subtype.ext (add_sub_cancel_right _ _)
  right_inv s := Subtype.ext (sub_add_cancel _ _)

theorem ternaryAffineSyndrome_card : Nat.card TernaryAffineSyndrome = 243 := by
  rw [← Nat.card_congr ternaryAffineSyndromeEquiv]
  letI := Fintype.ofEquiv
    (Fin (Module.finrank (ZMod 3) ternarySyndromeSum.ker) → ZMod 3)
    (Module.finBasis (ZMod 3) ternarySyndromeSum.ker).equivFun.symm.toEquiv
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3),
    ZMod.card, ternarySyndromeSum_ker_finrank]
  norm_num

end Atlas.Codes
