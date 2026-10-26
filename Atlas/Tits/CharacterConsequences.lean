import Atlas.Tits.Order

/-! Explicit two-element image and generation consequences for the actual
transfer character. No splitting or involutory complement is asserted. -/

namespace Atlas.Tits

/-- The complete image, not only its cardinality. -/
theorem mem_transfer_range_iff (u : (ZMod 5)ˣ) :
    u ∈ transfer.range ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    have hs := pow_card_eq_one' (x := (⟨u,hu⟩ : transfer.range))
    rw [transfer_range_order] at hs
    have hpow : u^2 = 1 := congrArg Subtype.val hs
    have hsmall : ∀ v : (ZMod 5)ˣ, v^2 = 1 → v = 1 ∨ v = -1 := by decide
    exact hsmall u hpow
  · rintro (rfl | rfl)
    · exact transfer.range.one_mem
    · exact ⟨localAlpha,transfer_alpha⟩

theorem transfer_range_set : (transfer.range : Set (ZMod 5)ˣ) = {1,-1} := by
  ext u
  change u ∈ transfer.range ↔ u = 1 ∨ u = -1
  exact mem_transfer_range_iff u

theorem alpha_square_mem_derived : localAlpha^2 ∈ derivedSubgroup := by
  rw [derived_eq_transferKernel]
  change transfer (localAlpha^2) = 1
  rw [map_pow,transfer_alpha]
  decide

theorem alpha_not_mem_derived : localAlpha ∉ derivedSubgroup := by
  rw [derived_eq_transferKernel]
  change transfer localAlpha ≠ 1
  rw [transfer_alpha]
  decide

/-- The literal subgroup model and the literal kernel model are equivalent. -/
noncomputable def modelEquivTransferKernel : Model ≃* transfer.ker :=
  MulEquiv.subgroupCongr derived_eq_transferKernel

/-- Alpha and the derived subgroup generate the ambient group; this says
nothing about splitting the index-two extension. -/
theorem ambient_generated_by_derived_alpha :
    derivedSubgroup ⊔ Subgroup.closure ({localAlpha} : Set Ambient) = ⊤ := by
  have hleft : derivedSubgroup ≤
      derivedSubgroup ⊔ Subgroup.closure ({localAlpha} : Set Ambient) := le_sup_left
  have hright : Subgroup.closure ({localAlpha} : Set Ambient) ≤
      derivedSubgroup ⊔ Subgroup.closure ({localAlpha} : Set Ambient) := le_sup_right
  apply top_unique
  intro g hg
  by_cases hm : g ∈ derivedSubgroup
  · exact hleft hm
  · have hi : localAlpha⁻¹ ∉ derivedSubgroup := by
      simpa only [Subgroup.inv_mem_iff] using alpha_not_mem_derived
    have hk : g*localAlpha⁻¹ ∈ derivedSubgroup :=
      (derivedSubgroup.mul_mem_iff_of_index_two index_derived).mpr (by simp [hm,hi])
    have ha : localAlpha ∈ derivedSubgroup ⊔ Subgroup.closure ({localAlpha} : Set Ambient) :=
      hright (Subgroup.subset_closure (Set.mem_singleton localAlpha))
    have h := (derivedSubgroup ⊔ Subgroup.closure ({localAlpha} : Set Ambient)).mul_mem
      (hleft hk) ha
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

end Atlas.Tits
