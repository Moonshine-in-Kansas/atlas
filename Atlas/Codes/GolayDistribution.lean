/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.GolayCounts

namespace Atlas.Codes
open scoped BigOperators
open Finset

def allOnes : BinaryWord := fun _ => 1

theorem allOnes_mem_C0 : allOnes ∈ C0 := by
  have hp : (fun _ : Fin 6 => (1 : Bit)) ∈ P6 := (parityCode_mem 5 _).mpr (by decide)
  refine ⟨(0,⟨_,hp⟩), ?_⟩
  simp [c0Encoder, rho, allOnes]
  rfl

theorem C0_le_golay : C0 ≤ golay := fun w hw => (golay_cosets w).mpr (Or.inl hw)

theorem complement_weight (w : BinaryWord) : hammingNorm (w + allOnes) + hammingNorm w = 24 := by
  have he := binary_weight_add w allOnes
  have hw : hammingNorm allOnes = 24 := by decide
  have ho : overlap w allOnes = hammingNorm w := by
    rw [overlap_eq_sum, hammingNorm_eq_sum]
    simp [allOnes]
  rw [hw, ho] at he
  omega

theorem golay_weights (w : golay) :
    hammingNorm w.val = 0 ∨ hammingNorm w.val = 8 ∨ hammingNorm w.val = 12 ∨
      hammingNorm w.val = 16 ∨ hammingNorm w.val = 24 := by
  have hc := complement_weight w.val
  have hd := golay_doublyEven w.val w.prop
  have hm := golay_minimum w.val w.prop
  have hm' := golay_minimum (w.val + allOnes)
    (golay.add_mem w.prop (C0_le_golay allOnes_mem_C0))
  have hz := hammingNorm_eq_zero (x := w.val)
  have hz' := hammingNorm_eq_zero (x := w.val + allOnes)
  by_cases h : w.val = 0
  · left; exact hz.mpr h
  by_cases h' : w.val + allOnes = 0
  · have := hz'.mpr h'
    omega
  have := hm h
  have := hm' h'
  omega

theorem weight_twentyfour_iff (w : BinaryWord) : hammingNorm w = 24 ↔ w = allOnes := by
  constructor
  · intro hw
    have hc := complement_weight w
    have hz : w + allOnes = 0 := hammingNorm_eq_zero.mp (by omega)
    funext i
    have hi := congrFun hz i
    have hh : ∀ x : Bit, x + 1 = 0 → x = 1 := by decide
    exact hh (w i) hi
  · rintro rfl
    decide

theorem code_extreme_count (C : Submodule Bit BinaryWord) [Fintype C]
    (ho : allOnes ∈ C) (k : ℕ) (hk : k = 0 ∨ k = 24) :
    Nat.card {w : C // hammingNorm w.val = k} = 1 := by
  classical
  rcases hk with rfl | rfl
  · let e : {w : C // hammingNorm w.val = 0} ≃ {w : C // w = 0} :=
      Equiv.subtypeEquivRight (fun w => by
        rw [hammingNorm_eq_zero]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
    rw [Nat.card_congr e]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · let e : {w : C // hammingNorm w.val = 24} ≃ {w : C // w = ⟨allOnes,ho⟩} :=
      Equiv.subtypeEquivRight (fun w => by
        rw [weight_twentyfour_iff]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
    rw [Nat.card_congr e]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem golay_weight_distribution (k : ℕ) : golayWeightCount k =
    if k = 0 then 1 else if k = 8 then 759 else if k = 12 then 2576 else
      if k = 16 then 759 else if k = 24 then 1 else 0 := by
  classical
  have h0 := code_extreme_count golay (C0_le_golay allOnes_mem_C0) 0 (Or.inl rfl)
  have h24 := code_extreme_count golay (C0_le_golay allOnes_mem_C0) 24 (Or.inr rfl)
  have h8 := golay_middle_counts 0
  have h12 := golay_middle_counts 1
  have h16 := golay_middle_counts 2
  by_cases hk0 : k = 0
  · subst k; simpa [golayWeightCount] using h0
  by_cases hk8 : k = 8
  · subst k; simpa [middleWeights] using h8
  by_cases hk12 : k = 12
  · subst k; simpa [middleWeights] using h12
  by_cases hk16 : k = 16
  · subst k; simpa [middleWeights] using h16
  by_cases hk24 : k = 24
  · subst k; simpa [golayWeightCount] using h24
  have hi : IsEmpty {w : golay // hammingNorm w.val = k} := ⟨by
    intro w
    have h := golay_weights w.val
    rw [w.prop] at h
    rcases h with h | h | h | h | h <;> contradiction⟩
  simp [golayWeightCount, Nat.card_eq_fintype_card, hk0, hk8, hk12, hk16, hk24]

theorem even_coset_distribution (k : ℕ) : evenCosetCount k =
    if k = 0 then 1 else if k = 8 then 375 else if k = 12 then 1296 else
      if k = 16 then 375 else if k = 24 then 1 else 0 := by
  classical
  have h0 := code_extreme_count C0 allOnes_mem_C0 0 (Or.inl rfl)
  have h24 := code_extreme_count C0 allOnes_mem_C0 24 (Or.inr rfl)
  have h8 := even_middle_counts 0
  have h12 := even_middle_counts 1
  have h16 := even_middle_counts 2
  by_cases hk0 : k = 0
  · subst k; simpa [evenCosetCount] using h0
  by_cases hk8 : k = 8
  · subst k; simpa [middleWeights] using h8
  by_cases hk12 : k = 12
  · subst k; simpa [middleWeights] using h12
  by_cases hk16 : k = 16
  · subst k; simpa [middleWeights] using h16
  by_cases hk24 : k = 24
  · subst k; simpa [evenCosetCount] using h24
  have hi : IsEmpty {w : C0 // hammingNorm w.val = k} := ⟨by
    intro w
    have h := golay_weights ⟨w.val.val,C0_le_golay w.val.prop⟩
    change hammingNorm w.val.val = 0 ∨ hammingNorm w.val.val = 8 ∨
      hammingNorm w.val.val = 12 ∨ hammingNorm w.val.val = 16 ∨ hammingNorm w.val.val = 24 at h
    rw [w.prop] at h
    rcases h with h | h | h | h | h <;> contradiction⟩
  simp [evenCosetCount, Nat.card_eq_fintype_card, hk0, hk8, hk12, hk16, hk24]

theorem odd_coset_distribution (k : ℕ) : oddCosetCount k =
    if k = 8 then 384 else if k = 12 then 1280 else if k = 16 then 384 else 0 := by
  have h := golayWeightCount_cosets k
  rw [golay_weight_distribution, even_coset_distribution] at h
  split_ifs at h ⊢ <;> omega

end Atlas.Codes
