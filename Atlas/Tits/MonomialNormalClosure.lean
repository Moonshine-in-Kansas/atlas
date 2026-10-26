import Atlas.Tits.ProjectiveSignIdentity

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
open scoped commutatorElement
set_option maxRecDepth 16384

/-- The actual monomial subgroup element represented by d. -/
noncomputable def monomialD : monomialPointGroup :=
  ⟨localD, ⟨⟨coupleCodeD, localCodeD_fixes_reference⟩, rfl⟩⟩

noncomputable def monomialN : monomialPointGroup := monomialD ^ 4
noncomputable def monomialNormalClosure : Subgroup monomialPointGroup :=
  Subgroup.normalClosure {monomialN}

theorem monomialNormalClosure_le_normal (N : Subgroup Ambient) [N.Normal]
    (hN : N ≠ ⊥) : monomialNormalClosure ≤ N.comap monomialPointGroup.subtype := by
  apply Subgroup.normalClosure_le_normal
  rintro x (rfl : x = monomialN)
  exact localN_mem_normal N hN

theorem localCodeV_fixes_reference : codeV ∈ codeReferenceStabilizer := by
  apply original_coordinate_cross_fix codeV seedVMonomial codeV_transport
  decide +kernel

noncomputable def monomialV : monomialPointGroup :=
  ⟨codePointHom ⟨codeV, localCodeV_fixes_reference⟩,
    ⟨⟨codeV, localCodeV_fixes_reference⟩, rfl⟩⟩

noncomputable def monomialSignWord : monomialPointGroup := ⁅⁅monomialN, monomialV⁆, monomialV⁆

theorem monomialSignWord_mem_normalClosure : monomialSignWord ∈ monomialNormalClosure := by
  letI : monomialNormalClosure.Normal := Subgroup.normalClosure_normal
  have hn : monomialN ∈ monomialNormalClosure :=
    Subgroup.subset_normalClosure (Set.mem_singleton monomialN)
  have hc (a : monomialPointGroup) (ha : a ∈ monomialNormalClosure) :
      ⁅a, monomialV⁆ ∈ monomialNormalClosure :=
    Subgroup.commutator_le_left monomialNormalClosure ⊤
      (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _))
  exact hc _ (hc _ hn)

/-- The normal-closure word is the required row sign in the actual scalar quotient. -/
theorem monomialSignWord_image :
    ambientStabilizer.subtype (monomialPointGroup.subtype monomialSignWord) =
      codeToRudvalis (seedARowSign (binaryLabel 4)) := by
  exact projective_double_commutator_sign

end Atlas.Tits
