import Atlas.LinearGroups.Chevalley.Comparison.TypeDNaturalInjective

/-! Separate projective and vector kernels of the actual D natural map.
The projective kernel is the full selected center. The vector kernel is the
kernel of its scalar character, and is not identified with the whole center.
Only new Model simplicity, not either old/new order formula, is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeD
open Classical Atlas.Orthogonal

variable (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] [Finite K]

/-- Injectivity after rho descent identifies the projective kernel exactly. -/
theorem naturalProjectiveHom_ker_eq_rhoKernel :
    (naturalProjectiveHom n hn K).ker =
      (selectedWeightCompanionRho (.D (n+2) hn) K).ker := by
  apply le_antisymm
  · intro g hg
    apply modelNaturalProjectiveHom_injective n hn K
    rw [modelNaturalProjectiveHom_rho, map_one]
    exact hg
  · exact rhoKernel_le_naturalProjectiveKernel n hn K

theorem naturalProjectiveHom_ker_eq_center :
    (naturalProjectiveHom n hn K).ker =
      Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K) :=
  (naturalProjectiveHom_ker_eq_rhoKernel n hn K).trans
    (selectedWeightCompanion_center_eq_rhoKernel (.D (n+2) hn) K).symm

/-- The natural vector kernel is contained in the full center. -/
theorem naturalElementaryHom_ker_le_center :
    (naturalElementaryHom n hn K).ker ≤
      Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K) := by
  rw [← naturalProjectiveHom_ker_eq_center n hn K]
  intro g hg
  change projectiveElementaryMap (formD (n+2) K) (naturalElementaryHom n hn K g)=1
  rw [show naturalElementaryHom n hn K g=1 from hg, map_one]

private def centerScalar
    (z : Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K)) : Kˣ :=
  (naturalOrthogonalHom_scalar_of_rho_eq_one n hn K z.val
    ((le_of_eq (selectedWeightCompanion_center_eq_rhoKernel (.D (n+2) hn) K))
      z.property)).choose

private theorem centerScalar_spec
    (z : Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K)) :
    (centerScalar n hn K z).val^2=1 ∧
      ∀ v, (naturalOrthogonalHom n hn K z.val).val v=(centerScalar n hn K z).val • v :=
  (naturalOrthogonalHom_scalar_of_rho_eq_one n hn K z.val
    ((le_of_eq (selectedWeightCompanion_center_eq_rhoKernel (.D (n+2) hn) K))
      z.property)).choose_spec

private theorem scalar_unique (c d : Kˣ)
    (h : ∀ v : Index n → K, c.val • v=d.val • v) : c=d := by
  apply Units.ext
  have he := congrFun (h (Pi.single (.inl (0 : Fin (n+2))) 1))
    (.inl (0 : Fin (n+2)))
  simpa [Pi.smul_apply, smul_eq_mul] using he

/-- The unique unit by which a central element acts on the natural space. -/
def naturalCenterCharacter :
    Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K) →* Kˣ where
  toFun := centerScalar n hn K
  map_one' := by
    apply scalar_unique n K
    intro v
    have h := (centerScalar_spec n hn K 1).2 v
    simp only [Subgroup.coe_one, map_one] at h
    change v = (centerScalar n hn K 1).val • v at h
    simpa only [Units.val_one, one_smul] using h.symm
  map_mul' z w := by
    apply scalar_unique n K
    intro v
    have hm : (naturalOrthogonalHom n hn K (z*w).val).val v=
        (naturalOrthogonalHom n hn K z.val).val
          ((naturalOrthogonalHom n hn K w.val).val v) := by
      rw [Subgroup.coe_mul, map_mul]
      rfl
    calc
      _ = (naturalOrthogonalHom n hn K (z*w).val).val v :=
        ((centerScalar_spec n hn K (z*w)).2 v).symm
      _ = _ := hm
      _ = _ := by
        rw [(centerScalar_spec n hn K w).2, (centerScalar_spec n hn K z).2,
          smul_smul]
        rfl

theorem naturalCenterCharacter_action
    (z : Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K))
    (v : Index n → K) :
    (naturalOrthogonalHom n hn K z.val).val v=(naturalCenterCharacter n hn K z).val • v :=
  (centerScalar_spec n hn K z).2 v

theorem naturalCenterCharacter_sq
    (z : Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K)) :
    (naturalCenterCharacter n hn K z).val^2=1 :=
  (centerScalar_spec n hn K z).1

/-- The vector kernel is characterized by scalar one inside the full center. -/
theorem naturalElementaryHom_eq_one_iff_center_character
    (g : SelectedWeightCompanion (.D (n+2) hn) K) :
    naturalElementaryHom n hn K g=1 ↔
      ∃ hz : g ∈ Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K),
        naturalCenterCharacter n hn K ⟨g,hz⟩=1 := by
  constructor
  · intro hg
    have hz := naturalElementaryHom_ker_le_center n hn K hg
    refine ⟨hz, ?_⟩
    apply scalar_unique n K
    intro v
    have he : naturalOrthogonalHom n hn K g=1 := congrArg Subtype.val hg
    have h := naturalCenterCharacter_action n hn K ⟨g,hz⟩ v
    rw [he] at h
    change v = (naturalCenterCharacter n hn K ⟨g,hz⟩).val • v at h
    simpa only [Units.val_one, one_smul] using h.symm
  · rintro ⟨hz,hzchar⟩
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (naturalOrthogonalHom n hn K g).val v=v
    rw [naturalCenterCharacter_action n hn K ⟨g,hz⟩ v, hzchar, Units.val_one,
      one_smul]

/-- The equality compares subgroups of the selected group via center inclusion. -/
theorem naturalElementaryHom_ker_eq_characterKernel_map :
    (naturalElementaryHom n hn K).ker =
      ((naturalCenterCharacter n hn K).ker).map
        (Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K)).subtype := by
  ext g
  constructor
  · intro hg
    obtain ⟨hz,hchar⟩ := (naturalElementaryHom_eq_one_iff_center_character n hn K g).mp hg
    exact ⟨⟨g,hz⟩,hchar,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact (naturalElementaryHom_eq_one_iff_center_character n hn K z.val).mpr
      ⟨z.property,hz⟩

end Atlas.Chevalley.Comparison.TypeD
