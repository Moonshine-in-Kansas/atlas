import Atlas.Rudvalis.CoupleMonomialGenerators
import Atlas.Rudvalis.ReferenceConfigurations

namespace Atlas.Rudvalis

noncomputable abbrev codeCoupleStabilizer : Subgroup codeGroup :=
  MulAction.stabilizer codeGroup localReferenceCross ⊓
    MulAction.stabilizer codeGroup referenceSecondCross

noncomputable def coupleGaussianHom : codeCoupleStabilizer →* gaussianLatticeGroup :=
  codeGaussianHom.comp codeCoupleStabilizer.subtype

noncomputable def coupleFusionGroup : Subgroup gaussianLatticeGroup :=
  Subgroup.closure (Set.range coupleGaussianHom ∪ {localFusionT})

theorem coupleGaussianHom_mem (g : codeCoupleStabilizer) :
    coupleGaussianHom g∈coupleFusionGroup :=
  Subgroup.subset_closure (Or.inl ⟨g,rfl⟩)

theorem localFusionT_mem_coupleFusionGroup : localFusionT∈coupleFusionGroup :=
  Subgroup.subset_closure (Or.inr rfl)

theorem coupleFusionGroup_le_generated : coupleFusionGroup≤generatedGaussianGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨a,rfl⟩|rfl)
  · exact codeGaussianHom_mem_generated a.val
  · exact localFusionT_mem_generated

theorem coupleFusionGroup_le_pair_stabilizer :
    coupleFusionGroup≤MulAction.stabilizer gaussianLatticeGroup localReferenceCross ⊓
      MulAction.stabilizer gaussianLatticeGroup referenceSecondCross := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨a,rfl⟩|rfl)
  · change (codeGaussianHom a.val • localReferenceCross=localReferenceCross) ∧
      (codeGaussianHom a.val • referenceSecondCross=referenceSecondCross)
    simp only [codeGaussianHom_cross]
    exact a.prop
  · exact ⟨localFusionT_fixes_first,localFusionT_fixes_second⟩

theorem coupleFusionGroup_fix (g : coupleFusionGroup) :
    g.val • localReferenceCross=localReferenceCross ∧
      g.val • referenceSecondCross=referenceSecondCross :=
  coupleFusionGroup_le_pair_stabilizer g.prop

theorem coupleFusionGroup_preserves_referenceCouple (g : coupleFusionGroup) :
    gaussianImage g.val referenceCouple=referenceCouple := by
  have h := coupleFusionGroup_fix g
  ext c
  simp only [gaussianImage,referenceCouple,Set.image_insert_eq,Set.image_singleton,h.1,h.2]

theorem coupleCodeR_mem : codeR∈codeCoupleStabilizer := coupleCodeR_fixes_reference

theorem coupleCodeBeta_mem : coupleCodeBeta∈codeCoupleStabilizer := coupleCodeBeta_fixes_reference

theorem codeCoupleOrbit_subset_coupleFusionOrbit (y : MinimalCross) :
    MulAction.orbit codeCoupleStabilizer y⊆MulAction.orbit coupleFusionGroup y := by
  intro c hc
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hc
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨⟨coupleGaussianHom g,coupleGaussianHom_mem g⟩,?_⟩
  change codeGaussianHom g.val • y=c
  rw [codeGaussianHom_cross]
  exact hg

noncomputable def codeCoupleIteratedStabilizerEquiv : codeCoupleStabilizer ≃
    MulAction.stabilizer codeReferenceStabilizer referenceSecondCross :=
  { toFun := fun g=>⟨⟨g.val,g.prop.1⟩,g.prop.2⟩
    invFun := fun g=>⟨g.val.val,g.val.prop,g.prop⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }

theorem codeCoupleStabilizer_order : Nat.card codeCoupleStabilizer=16384 := by
  rw [Nat.card_congr codeCoupleIteratedStabilizerEquiv]
  change Nat.card (MulAction.stabilizer (MulAction.stabilizer codeGroup localReferenceCross) referenceSecondCross)=16384
  rw [localReferenceCross_eq,referenceSecondCross_eq]
  exact coordinate_same_row_pair_stabilizer_order (rowLabel 0) 0 (binaryLabel 2)
    (by simpa only [←localReferenceCross_eq,←referenceSecondCross_eq] using Ne.symm reference_crosses_ne)

end Atlas.Rudvalis
