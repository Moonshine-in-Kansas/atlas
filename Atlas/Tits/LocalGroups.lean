import Atlas.Rudvalis.ProjectiveCrossFaithful
import Atlas.Rudvalis.CoupleFusionOrbits
import Mathlib.GroupTheory.Commutator.Basic

/-! The actual projective cross stabilizer and its derived subgroup.
No Tits order, simplicity, transfer, or global Rudvalis simplicity is used. -/
namespace Atlas.Tits
open Atlas.Rudvalis

noncomputable def ambientStabilizer : Subgroup RudvalisGroup :=
  MulAction.stabilizer RudvalisGroup localReferenceCross

abbrev Ambient := ↥ambientStabilizer

/-- Orthogonal minimal crosses in the inherited lattice geometry. -/
def Neighbours := {c : MinimalCross // CrossOrthogonal localReferenceCross c}

noncomputable def referenceNeighbour : Neighbours :=
  ⟨referenceSecondCross,reference_crosses_orthogonal⟩

theorem cardAmbient : Nat.card Ambient=35942400 :=
  rudvalis_point_stabilizer_order _

theorem cardNeighbours : Nat.card Neighbours=1755 := rudvalis_orthogonal_degree _

theorem projective_orthogonal (g : RudvalisGroup) (a b : MinimalCross) :
    CrossOrthogonal (g • a) (g • b) ↔ CrossOrthogonal a b := by
  induction g using QuotientGroup.induction_on with
  | H g => exact crossOrthogonal_gaussian g a b

noncomputable instance neighbourAction : MulAction Ambient Neighbours where
  smul g c := ⟨g.val • c.val,by
    have h := (projective_orthogonal g.val localReferenceCross c.val).mpr c.prop
    rw [show g.val • localReferenceCross=localReferenceCross from g.prop] at h
    exact h⟩
  one_smul c := Subtype.ext (one_smul _ _)
  mul_smul g h c := Subtype.ext (mul_smul _ _ _)

@[simp] theorem neighbour_smul_val (g : Ambient) (c : Neighbours) :
    (g • c).val=g.val • c.val := rfl

noncomputable def localProjection : localFusionGroup →* Ambient where
  toFun g := ⟨QuotientGroup.mk g.val,localFusionGroup_fix g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem localProjection_surjective : Function.Surjective localProjection := by
  intro g
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective gaussianScalarSubgroup g.val
  have hx : a • localReferenceCross=localReferenceCross := by
    change (QuotientGroup.mk a : RudvalisGroup) • localReferenceCross=localReferenceCross
    rw [show (QuotientGroup.mk a : RudvalisGroup)=g.val from ha]
    exact g.prop
  refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
  rw [localFusionGroup_eq_point_stabilizer]
  exact hx

noncomputable instance neighboursTransitive : MulAction.IsPretransitive Ambient Neighbours where
  exists_smul_eq a b := by
    have ha : a.val∈MulAction.orbit localFusionGroup localThirdCross := by
      rw [localFusionGroup_orthogonal_orbit];exact a.prop
    have hb : b.val∈MulAction.orbit localFusionGroup localThirdCross := by
      rw [localFusionGroup_orthogonal_orbit];exact b.prop
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ha
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hb
    refine ⟨localProjection (h*g⁻¹),Subtype.ext ?_⟩
    change (h*g⁻¹) • a.val=b.val
    rw [mul_smul,←hg,inv_smul_smul,hh]

instance neighboursFaithful : FaithfulSMul Ambient Neighbours := by
  apply faithfulSMul_iff.mpr
  intro g hg
  apply Subtype.ext
  apply rudvalis_perpendicular_kernel localReferenceCross g.val g.prop
  intro c hc
  exact congrArg Subtype.val (hg (⟨c,hc⟩ : Neighbours))

noncomputable def pairStabilizer : Subgroup Ambient :=
  MulAction.stabilizer Ambient referenceNeighbour

noncomputable instance : Finite Neighbours := inferInstanceAs
  (Finite {c : MinimalCross // CrossOrthogonal localReferenceCross c})

theorem cardPairStabilizer : Nat.card pairStabilizer=20480 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Ambient referenceNeighbour)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_univ,cardNeighbours,cardAmbient] at h
  change 1755*Nat.card pairStabilizer=35942400 at h
  omega

/-- The target is the actual commutator subgroup, not a numerical group model. -/
noncomputable def derivedSubgroup : Subgroup Ambient := commutator Ambient
abbrev Model := ↥derivedSubgroup

noncomputable def embeddingIntoRudvalis : Model →* RudvalisGroup :=
  ambientStabilizer.subtype.comp derivedSubgroup.subtype

theorem embeddingIntoRudvalis_injective : Function.Injective embeddingIntoRudvalis :=
  ambientStabilizer.subtype_injective.comp derivedSubgroup.subtype_injective

noncomputable def codePointHom : codeReferenceStabilizer →* Ambient where
  toFun g := ⟨QuotientGroup.mk (codeGaussianHom g.val),by
    change codeGaussianHom g.val • localReferenceCross=localReferenceCross
    rw [codeGaussianHom_cross];exact g.prop⟩
  map_one' := Subtype.ext (map_one ((QuotientGroup.mk' gaussianScalarSubgroup).comp
    (codeGaussianHom.comp codeReferenceStabilizer.subtype)))
  map_mul' g h := Subtype.ext (map_mul ((QuotientGroup.mk' gaussianScalarSubgroup).comp
    (codeGaussianHom.comp codeReferenceStabilizer.subtype)) g h)

noncomputable def monomialPointGroup : Subgroup Ambient := codePointHom.range

noncomputable def coupleProjection : coupleFusionGroup →* pairStabilizer where
  toFun g := ⟨⟨QuotientGroup.mk g.val,(coupleFusionGroup_fix g).1⟩,
    Subtype.ext (coupleFusionGroup_fix g).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coupleProjection_surjective : Function.Surjective coupleProjection := by
  intro g
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective gaussianScalarSubgroup g.val.val
  have hx : a • localReferenceCross=localReferenceCross := by
    change (QuotientGroup.mk a : RudvalisGroup) • localReferenceCross=localReferenceCross
    rw [show (QuotientGroup.mk a : RudvalisGroup)=g.val.val from ha]
    exact g.val.prop
  have hy : a • referenceSecondCross=referenceSecondCross := by
    change (QuotientGroup.mk a : RudvalisGroup) • referenceSecondCross=referenceSecondCross
    rw [show (QuotientGroup.mk a : RudvalisGroup)=g.val.val from ha]
    exact congrArg Subtype.val g.prop
  refine ⟨⟨a,?_⟩,Subtype.ext (Subtype.ext ha)⟩
  rw [coupleFusionGroup_eq_pair_stabilizer]
  exact ⟨hx,hy⟩

end Atlas.Tits
