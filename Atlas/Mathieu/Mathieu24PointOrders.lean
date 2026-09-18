/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.Mathieu24FiveTransitive

noncomputable section
namespace Atlas.Codes

/-- The actual subgroup fixing the entries of an ordered tuple of distinct coordinates. -/
def orderedPointStabilizer {k : ℕ} (e : Fin k ↪ Omega) : Subgroup Mathieu24CodeModel :=
  fixingSubgroup Mathieu24CodeModel (Set.range e)

theorem orderedPointStabilizer_order_product {k : ℕ} (e : Fin k ↪ Omega) (hk : k ≤ 5) :
    Nat.card (orderedPointStabilizer e) * ((24).choose k * k.factorial) = 244823040 := by
  letI := mathieu24_five_transitive
  have hn : (Set.range e).ncard = k := by
    rw [Set.ncard_range_of_injective e.injective]
    simp
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega (Set.range e).ncard := by
    rw [hn]
    apply MulAction.isMultiplyPretransitive_of_le hk
    norm_num [Omega,HexIndex]
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht
  have hc : Nat.card Omega = 24 := by simp [Omega,HexIndex]
  rw [hn,hc] at hi
  have he := (orderedPointStabilizer e).card_mul_index
  change (orderedPointStabilizer e).index = Nat.choose 24 k * k.factorial at hi
  rw [hi,mathieu24_order] at he
  exact he

theorem mathieu24_one_point_order (e : Fin 1 ↪ Omega) : Nat.card (orderedPointStabilizer e) = 10200960 := by
  have h := orderedPointStabilizer_order_product e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu24_two_point_order (e : Fin 2 ↪ Omega) : Nat.card (orderedPointStabilizer e) = 443520 := by
  have h := orderedPointStabilizer_order_product e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu24_three_point_order (e : Fin 3 ↪ Omega) : Nat.card (orderedPointStabilizer e) = 20160 := by
  have h := orderedPointStabilizer_order_product e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu24_four_point_order (e : Fin 4 ↪ Omega) : Nat.card (orderedPointStabilizer e) = 960 := by
  have h := orderedPointStabilizer_order_product e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

theorem mathieu24_five_point_order (e : Fin 5 ↪ Omega) : Nat.card (orderedPointStabilizer e) = 48 := by
  have h := orderedPointStabilizer_order_product e (by decide)
  norm_num [Nat.choose,Nat.factorial] at h
  omega

end Atlas.Codes
