import Atlas.Conway.EisensteinProjectiveModel
import Atlas.Conway.LeechCentralQuotient

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem eisensteinUnitIsometries_negation :
    (eisensteinCentralizerEquiv (eisensteinUnitIsometries (-1))).val = negationIsometry := by
  have he := rationalExtension_unique negationIsometry.val
    (-LinearMap.id : RationalCoordinates →ₗ[ℚ] RationalCoordinates) (by
      intro x; rw [negationIsometry_apply]; simp)
  apply fullIsometryEquiv.injective
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := eisensteinComparison.surjective x
  rw [eisensteinUnitIsometries_Co0_agrees]
  change eisensteinComparison (eisensteinToRational (-1) • z) =
    rationalExtension negationIsometry.val (eisensteinComparison z)
  have hh := LinearMap.congr_fun he (eisensteinComparison z)
  simpa only [map_neg, map_one, neg_one_smul, LinearMap.neg_apply, LinearMap.id_apply, LinearEquiv.coe_coe] using hh

theorem leechCentralSigns_le_eisensteinCentralizer : leechCentralSigns ≤ eisensteinCentralizer := by
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := Subgroup.mem_center_iff.mp (leechCentralSigns_eq_center ▸ hg) eisensteinRho
  exact h.symm

/-- The sign subgroup inside the actual scalar centralizer. -/
def eisensteinCentralizerSigns : Subgroup eisensteinCentralizer :=
  leechCentralSigns.comap eisensteinCentralizer.subtype

instance eisensteinCentralizerSigns_normal : eisensteinCentralizerSigns.Normal := by
  unfold eisensteinCentralizerSigns
  infer_instance

theorem eisensteinCentralizerSigns_card : Nat.card eisensteinCentralizerSigns = 2 := by
  have he := Subgroup.subgroupOfEquivOfLe leechCentralSigns_le_eisensteinCentralizer
  exact (Nat.card_congr he.toEquiv).trans leechCentralSigns_card

/-- Quotienting only by the signs retains the triple extension required for Co1. -/
abbrev EisensteinTripleModel := eisensteinCentralizer ⧸ eisensteinCentralizerSigns

/-- Natural comparison with the actual Conway central quotient. -/
def eisensteinTripleToCo1 : EisensteinTripleModel →* LeechCentralQuotient :=
  QuotientGroup.map _ _ eisensteinCentralizer.subtype le_rfl

theorem eisensteinTripleToCo1_injective : Function.Injective eisensteinTripleToCo1 := by
  apply (MonoidHom.ker_eq_bot_iff eisensteinTripleToCo1).mp
  rw [eisensteinTripleToCo1, QuotientGroup.ker_map]
  exact QuotientGroup.map_mk'_self _

theorem eisensteinTripleToCo1_mk (g : eisensteinCentralizer) :
    eisensteinTripleToCo1 (QuotientGroup.mk g) = leechCentralProjection g.val := rfl

theorem eisensteinCentralizerSigns_le_scalars :
    eisensteinCentralizerSigns ≤ eisensteinCentralizerScalars := by
  intro g hg
  rcases (leechCentralSigns_mem g.val).mp hg with he | he
  · have h : g = 1 := Subtype.ext he
    rw [h]
    exact eisensteinCentralizerScalars.one_mem
  · have h : g = eisensteinCentralizerEquiv (eisensteinUnitIsometries (-1)) :=
      Subtype.ext (he.trans eisensteinUnitIsometries_negation.symm)
    rw [h]
    apply Subgroup.mem_map.mpr
    refine ⟨eisensteinUnitIsometries (-1), ?_, rfl⟩
    rw [← eisensteinUnitIsometries_range]
    exact ⟨-1, rfl⟩

/-- The map from the sign quotient to the full six-scalar quotient. -/
def eisensteinTripleProjection : EisensteinTripleModel →* EisensteinProjectiveModel :=
  QuotientGroup.map _ _ (MonoidHom.id _) eisensteinCentralizerSigns_le_scalars

theorem eisensteinTripleProjection_surjective : Function.Surjective eisensteinTripleProjection := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective eisensteinCentralizerScalars y
  exact ⟨QuotientGroup.mk g, rfl⟩

theorem eisensteinTripleProjection_kernel :
    eisensteinTripleProjection.ker = eisensteinCentralizerScalars.map
      (QuotientGroup.mk' eisensteinCentralizerSigns) := by
  rw [eisensteinTripleProjection, QuotientGroup.ker_map]
  rfl

theorem eisensteinTripleProjection_kernel_card : Nat.card eisensteinTripleProjection.ker = 3 := by
  let f := (QuotientGroup.mk' eisensteinCentralizerSigns).comp
    eisensteinCentralizerScalars.subtype
  have hk : f.ker = eisensteinCentralizerSigns.subgroupOf eisensteinCentralizerScalars := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hkc : Nat.card f.ker = 2 := by
    rw [hk]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe eisensteinCentralizerSigns_le_scalars).toEquiv).trans
        eisensteinCentralizerSigns_card
  have hr : f.range = eisensteinTripleProjection.ker := by
    dsimp only [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype, eisensteinTripleProjection_kernel]
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [eisensteinCentralizerScalars_order, hkc,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hr] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hc.symm

theorem eisensteinTripleProjection_kernel_central :
    eisensteinTripleProjection.ker ≤ Subgroup.center EisensteinTripleModel := by
  rw [eisensteinTripleProjection_kernel]
  rintro g ⟨z, hz, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective eisensteinCentralizerSigns h
  rw [← map_mul, ← map_mul]
  exact congrArg (QuotientGroup.mk' eisensteinCentralizerSigns)
    (Subgroup.mem_center_iff.mp (eisensteinCentralizerScalars_le_center hz) x)

end Atlas.Conway
