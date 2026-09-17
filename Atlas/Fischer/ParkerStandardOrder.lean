import Atlas.Fischer.ParkerStandardKernel
import Atlas.Fischer.ParkerStandardParity
import Atlas.Fischer.ParkerStandardSurjectivity
import Atlas.Mathieu.Mathieu24Order
import Mathlib.GroupTheory.Index

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerStandardProjection_index :
    parkerStandardProjection.ker.index = Nat.card Mathieu24CodeModel := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr parkerStandardProjection_surjective,
    Subgroup.card_top]

theorem parkerStandardGroup_order :
    Nat.card ParkerStandardGroup = 4096 * Nat.card Mathieu24CodeModel := by
  rw [← parkerStandardProjection.ker.card_mul_index,
    parkerStandardProjection_kernel_card, parkerStandardProjection_index]

theorem parkerStandardGroup_order_value : Nat.card ParkerStandardGroup = 1002795171840 := by
  rw [parkerStandardGroup_order, mathieu24_order]

theorem parkerStandardParity_cocode (d : Cocode) :
    parkerStandardParity (parkerCocodeStandard d) = Multiplicative.ofAdd (cocodeParity d) := by
  change Multiplicative.ofAdd (0 + cocodeDualEquiv d golayOne) =
    Multiplicative.ofAdd (cocodeDualEquiv d golayOne)
  rw [zero_add]

theorem parkerStandardParity_surjective : Function.Surjective parkerStandardParity := by
  intro s
  obtain ⟨d, hd⟩ := cocodeParity_surjective s.toAdd
  refine ⟨parkerCocodeStandard d, ?_⟩
  rw [parkerStandardParity_cocode, hd]
  rfl

noncomputable def parkerStandardPlusProjection : parkerStandardPlus →* Mathieu24CodeModel :=
  parkerStandardProjection.comp parkerStandardPlus.subtype

theorem parkerStandardPlusProjection_surjective :
    Function.Surjective parkerStandardPlusProjection := by
  intro g
  obtain ⟨e, he⟩ := parkerStandardProjection_surjective g
  obtain ⟨d, hd⟩ := cocodeParity_surjective (parkerStandardParity e).toAdd
  have hx : parkerCocodeStandard d * e ∈ parkerStandardPlus := by
    change parkerStandardParity (parkerCocodeStandard d * e) = 1
    rw [map_mul, parkerStandardParity_cocode, hd]
    change Multiplicative.ofAdd ((parkerStandardParity e).toAdd +
      (parkerStandardParity e).toAdd) = Multiplicative.ofAdd 0
    have h : ∀ x : Bit, x + x = 0 := by decide
    rw [h]
  refine ⟨⟨parkerCocodeStandard d * e, hx⟩, ?_⟩
  change parkerStandardProjection (parkerCocodeStandard d * e) = g
  rw [map_mul, parkerCocodeStandard_projection, one_mul, he]

theorem parkerStandardPlus_index : parkerStandardPlus.index = 2 := by
  change parkerStandardParity.ker.index = 2
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr parkerStandardParity_surjective,
    Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative Bit ≃ Bit)]
  simp [Nat.card_eq_fintype_card, Bit, ZMod.card]

theorem parkerStandardPlus_order :
    Nat.card parkerStandardPlus = 2048 * Nat.card Mathieu24CodeModel := by
  have h := parkerStandardPlus.card_mul_index
  rw [parkerStandardPlus_index, parkerStandardGroup_order] at h
  omega

theorem parkerStandardPlus_order_value : Nat.card parkerStandardPlus = 501397585920 := by
  rw [parkerStandardPlus_order, mathieu24_order]

end Atlas.Fischer
