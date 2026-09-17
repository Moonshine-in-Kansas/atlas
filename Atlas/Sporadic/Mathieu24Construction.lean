/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Sporadic.Mathieu24
import Atlas.Mathieu.Mathieu24Simplicity
import Atlas.Codes.GolayPackage

/-! Complete public construction, preserving the original Job 6 API. -/

namespace Atlas.Sporadic.Mathieu24

/-- Expected group order; the pre-existing `order` theorem remains unchanged. -/
def expectedOrder : ℕ := 244823040

theorem card : Nat.card Model = expectedOrder := Atlas.Codes.mathieu24_order

theorem isSimpleGroup : IsSimpleGroup Model := Atlas.Codes.mathieu24_simple

theorem exists_mul_ne_mul : ∃ g h : Model, g * h ≠ h * g :=
  Atlas.Codes.mathieu24_noncommuting_pair

theorem card_factorization : Nat.card Model = 2^10 * 3^3 * 5 * 7 * 11 * 23 :=
  Atlas.Codes.mathieu24_order_factorization

theorem code_design_automorphisms :
    Atlas.Codes.codeAutomorphisms = Atlas.Codes.octadAutomorphisms :=
  Atlas.Codes.codeAutomorphisms_eq_octadAutomorphisms

theorem octads_design (T : Finset Points) (hT : T.card = 5) :
    ∃! O : Finset Points, O ∈ Atlas.Codes.octads ∧ T ⊆ O :=
  Atlas.Codes.octad_steiner T hT

theorem sextet_transitive : MulAction.IsPretransitive Model Atlas.Codes.UnorderedSextet :=
  Atlas.Codes.unorderedSextet_pretransitive

theorem sextet_count : Nat.card Atlas.Codes.UnorderedSextet = 1771 :=
  Atlas.Codes.unordered_sextets_card

noncomputable def sextetOrbitStabilizerEquiv :
    Atlas.Codes.UnorderedSextet × Atlas.Codes.SextetStabilizer ≃ Model :=
  Atlas.Codes.sextetOrbitStabilizerEquiv

theorem sextet_stabilizer_order : Nat.card Atlas.Codes.SextetStabilizer = 138240 :=
  Atlas.Codes.sextetStabilizer_card

theorem pointwise_stabilizer_order_product {k : ℕ} (e : Fin k ↪ Points) (hk : k ≤ 5) :
    Nat.card (Atlas.Codes.orderedPointStabilizer e) * ((24).choose k * k.factorial) = expectedOrder :=
  Atlas.Codes.orderedPointStabilizer_order_product e hk

/-- All fields concern the retained two-twist code, its coordinates, and its full group. -/
structure Construction : Prop where
  code : Atlas.Codes.GolayFromTrio
  action : Atlas.Codes.Mathieu24HexacodeConstructionPackage
  full_code_design : Atlas.Codes.codeAutomorphisms = Atlas.Codes.octadAutomorphisms
  simple : IsSimpleGroup Model
  point_stabilizers_simple : ∀ a : Points, IsSimpleGroup (Atlas.Codes.Mathieu23PointModel a)

/-- The final package; `construction` is retained as the original Job 6 theorem. -/
theorem construction_complete : Construction where
  code := Atlas.Codes.golay_from_trio
  action := Atlas.Codes.mathieu24_hexacode_construction
  full_code_design := code_design_automorphisms
  simple := isSimpleGroup
  point_stabilizers_simple := Atlas.Codes.mathieu23_simple

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧ Finite G ∧
    Nat.card G = expectedOrder ∧ IsSimpleGroup G ∧ (∃ g h : G, g * h ≠ h * g) ∧ Construction :=
  ⟨Model, inferInstance, ⟨MulEquiv.refl _⟩, finite, card, isSimpleGroup,
    exists_mul_ne_mul, construction_complete⟩

end Atlas.Sporadic.Mathieu24
