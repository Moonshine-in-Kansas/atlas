import Atlas.Rudvalis.SignPatterns
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The four-dimensional Hamming code indexing row signs. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def rowMoment : (Point → Bit) →ₗ[Bit] E where
  toFun a := ∑ p : Point, a p • p.val
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a b := by simp [mul_smul,Finset.smul_sum]

def hammingSignCode : Submodule Bit (Point → Bit) := rowMoment.ker

def rowMomentSection (v : E) : Point → Bit := fun p =>
  if p=basisPoint 0 then v 0 else if p=basisPoint 1 then v 1
    else if p=basisPoint 2 then v 2 else 0

theorem rowMomentSection_right (v : E) : rowMoment (rowMomentSection v)=v := by
  obtain ⟨i,rfl⟩ := binaryLabel_bijective.surjective v
  change rowMoment (rowMomentSection (binaryLabel i))=binaryLabel i
  decide +kernel +revert

theorem rowMoment_surjective : Function.Surjective rowMoment :=
  fun v => ⟨rowMomentSection v,rowMomentSection_right v⟩

theorem hammingSignCode_finrank : Module.finrank Bit hammingSignCode=4 := by
  have h := LinearMap.finrank_range_add_finrank_ker rowMoment
  rw [LinearMap.range_eq_top.mpr rowMoment_surjective,finrank_top] at h
  have hE : Module.finrank Bit E=3 := by simp [E,Module.finrank_pi_fintype]
  have hP : Module.finrank Bit (Point → Bit)=7 := by simp [Module.finrank_pi_fintype]
  change Module.finrank Bit E+Module.finrank Bit hammingSignCode=Module.finrank Bit (Point → Bit) at h
  rw [hE,hP] at h
  omega

theorem hammingSignCode_card : Nat.card hammingSignCode=16 := by
  classical
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=Bit),hammingSignCode_finrank]
  norm_num [Bit,ZMod.card]

end Atlas.Rudvalis
