/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.SextetReconstruction
import Atlas.Mathieu.HexacodeSextetPackage
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive

noncomputable section
namespace Atlas.Codes

theorem sextet_from_distinguished (S : UnorderedSextet) :
    ∃ g : Mathieu24CodeModel, g • distinguishedUnorderedSextet = S := by
  obtain ⟨g,hg⟩ := sextet_equivalent_distinguished S
  exact ⟨g⁻¹,by rw [← hg,inv_smul_smul]⟩

/-- Transitivity is derived from hexacode uniqueness and marked reconstruction. -/
theorem unorderedSextet_pretransitive : MulAction.IsPretransitive Mathieu24CodeModel UnorderedSextet :=
  (MulAction.isPretransitive_iff_base distinguishedUnorderedSextet).mpr sextet_from_distinguished

/-- The actual orbit, identified with all unordered sextets. -/
def sextetOrbitEquiv : MulAction.orbit Mathieu24CodeModel distinguishedUnorderedSextet ≃
    UnorderedSextet := Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
      intro S
      exact ⟨⟨S,(MulAction.mem_orbit_iff).mpr (sextet_from_distinguished S)⟩,rfl⟩⟩

/-- The orbit–stabilizer bijection for the retained full code automorphism group. -/
def sextetOrbitStabilizerEquiv : UnorderedSextet × SextetStabilizer ≃ Mathieu24CodeModel :=
  (sextetOrbitEquiv.symm.prodCongr (Equiv.refl _)).trans
    (MulAction.orbitProdStabilizerEquivGroup Mathieu24CodeModel distinguishedUnorderedSextet)

theorem mathieu24_order : Nat.card Mathieu24CodeModel = 244823040 := by
  rw [← Nat.card_congr sextetOrbitStabilizerEquiv,Nat.card_prod,
    unordered_sextets_card,sextetStabilizer_card]

theorem mathieu24_order_factorization :
    Nat.card Mathieu24CodeModel = 2^10 * 3^3 * 5 * 7 * 11 * 23 := by
  rw [mathieu24_order]
  norm_num

theorem sextetStabilizer_index : sextetStabilizer.index = 1771 := by
  rw [Subgroup.index_eq_card]
  change Nat.card (Mathieu24CodeModel ⧸ MulAction.stabilizer Mathieu24CodeModel
    distinguishedUnorderedSextet) = 1771
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Mathieu24CodeModel
    distinguishedUnorderedSextet),Nat.card_congr sextetOrbitEquiv,unordered_sextets_card]

end Atlas.Codes
