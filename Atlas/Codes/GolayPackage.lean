/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.GolayAutomorphisms
import Atlas.Codes.GolayRecovery
import Atlas.Codes.WeightEnumerators

namespace Atlas.Codes
open scoped BigOperators Polynomial

/-- The package is about the concrete two-twist code on the retained coordinates. -/
structure GolayFromTrio : Prop where
  coordinates : Nat.card Omega = 24
  seed_dimension : Module.finrank Bit trio = 3
  seed_cardinality : Nat.card trio = 8
  seed_duality : trio = dual trio
  first_gluing : Nonempty ((trio × E0) ≃ₗ[Bit] H0)
  first_twist : Nonempty ((trio × E0 × Bit) ≃ₗ[Bit] hexacode)
  first_encoding : ∀ x e ε, (firstTwist (x,e,ε) : HexWord) = phiWord x + e + ε • tau
  hex_dimension : Module.finrank Bit hexacode = 6
  hex_cardinality : Nat.card hexacode = 64
  hex_duality : hexacode = dual hexacode
  hex_minimum : ∀ w ∈ hexacode, w ≠ 0 → 4 ≤ hammingNorm w
  hex_distribution : ∀ k, hexWeightCount k =
    if k = 0 then 1 else if k = 4 then 45 else if k = 6 then 18 else 0
  second_twist : Nonempty ((hexacode × P6 × Bit) ≃ₗ[Bit] golay)
  second_encoding : ∀ h r ε, (golayEquiv (h,r,ε) : BinaryWord) = jWord h.val + rho r.val + ε • eta
  decoding : ∀ h r ε, golayRawDecoder (golayEncoder (h,r,ε)) = (h.val,r.val,ε)
  dimension : Module.finrank Bit golay = 12
  cardinality : Nat.card golay = 4096
  self_dual : golay = binaryDot.orthogonal golay
  doubly_even : ∀ w ∈ golay, 4 ∣ hammingNorm w
  minimum : ∀ w ∈ golay, w ≠ 0 → 8 ≤ hammingNorm w
  minimum_witness : eta ∈ golay ∧ hammingNorm eta = 8
  distance : ∀ u v : golay, u ≠ v → 8 ≤ hammingDist u.val v.val
  distribution : ∀ k, golayWeightCount k =
    if k = 0 then 1 else if k = 8 then 759 else if k = 12 then 2576 else
      if k = 16 then 759 else if k = 24 then 1 else 0
  enumerator : golayEnumerator = 1 + 759 * Polynomial.X^8 + 2576 * Polynomial.X^12 +
    759 * Polynomial.X^16 + Polynomial.X^24
  octad_basis : (∀ i, (golayBasis i : BinaryWord) = golayGenerators i) ∧
    (∀ i, hammingNorm (golayBasis i : BinaryWord) = 8)
  octads_generate : Submodule.span Bit octadWords = golay
  octad_count : octads.card = 759
  octad_sizes : ∀ O ∈ octads, O.card = 8
  steiner : ∀ T : Finset Omega, T.card = 5 → ∃! O : Finset Omega, O ∈ octads ∧ T ⊆ O
  sextet : IsSextet tetrad
  trio_octads : ∀ i, distinguishedTrio i ∈ octads
  trio_partition : ∀ p, ∃! i, p ∈ distinguishedTrio i
  marking_sizes : ∀ (m : KleinianMarking) t, (markedPair m t).card = 2
  marking_partition : ∀ (m : KleinianMarking) p, ∃! t, p ∈ markedPair m t
  marking_tetrads : ∀ (m : KleinianMarking) t, markedPair m t ⊆ tetrad t.1
  even_block_recovery : ∀ w, w ∈ C0 ↔ w ∈ golay ∧ ∀ i, Even (hammingNorm (fun k => w (i,k)))
  recover_hex_surjective : Function.Surjective recoverHex
  recover_hex_kernel : ∀ w : C0, recoverHex w = 0 ↔ w.val ∈ R0
  recover_hex_values : ∀ (w : C0) i, (recoverHex w).val i = blockDecode (fun k => w.val (i,k))
  recover_trio_surjective : Function.Surjective recoverTrio
  recover_trio_kernel : ∀ w : H0, recoverTrio w = 0 ↔ w.val ∈ E0
  automorphisms : codeAutomorphisms = octadAutomorphisms
  automorphisms_finite : Finite Mathieu24CodeModel
  automorphisms_faithful : FaithfulSMul Mathieu24CodeModel Omega

theorem golay_from_trio : GolayFromTrio where
  coordinates := by norm_num [Omega, HexIndex, Nat.card_eq_fintype_card]
  seed_dimension := trio_finrank
  seed_cardinality := trio_card
  seed_duality := trio_selfDual
  first_gluing := ⟨firstGluing⟩
  first_twist := ⟨firstTwist⟩
  first_encoding := firstTwist_apply
  hex_dimension := hexacode_finrank
  hex_cardinality := hexacode_card
  hex_duality := hexacode_selfDual
  hex_minimum := hexacode_minimum
  hex_distribution := hexacode_weight_distribution
  second_twist := ⟨golayEquiv⟩
  second_encoding := golayEquiv_apply
  decoding := golay_decode_encode
  dimension := golay_finrank
  cardinality := golay_card
  self_dual := golay_selfDual
  doubly_even := golay_doublyEven
  minimum := golay_minimum
  minimum_witness := ⟨eta_mem_golay,eta_weight⟩
  distance := golay_distance
  distribution := golay_weight_distribution
  enumerator := golayEnumerator_eq
  octad_basis := golay_octad_basis
  octads_generate := octads_span
  octad_count := octads_card
  octad_sizes := octad_size
  steiner := octad_steiner
  sextet := distinguished_sextet
  trio_octads := distinguishedTrio_octads
  trio_partition := distinguishedTrio_partition
  marking_sizes := markedPair_card
  marking_partition := markedPairs_partition
  marking_tetrads := markedPair_subset_tetrad
  even_block_recovery := C0_even_blocks
  recover_hex_surjective := recoverHex_surjective
  recover_hex_kernel := recoverHex_kernel
  recover_hex_values := recoverHex_blocks
  recover_trio_surjective := recoverTrio_surjective
  recover_trio_kernel := recoverTrio_kernel
  automorphisms := codeAutomorphisms_eq_octadAutomorphisms
  automorphisms_finite := codeAutomorphisms_finite
  automorphisms_faithful := codeAutomorphisms_faithful

theorem exists_golay_from_trio :
    ∃ C : Submodule Bit BinaryWord, C = golay ∧ GolayFromTrio :=
  ⟨golay,rfl,golay_from_trio⟩

end Atlas.Codes
