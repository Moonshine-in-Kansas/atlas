import Atlas.Rudvalis.ProjectiveSimplicity
import Atlas.Rudvalis.ProjectiveFrameEmbedding
import Atlas.Rudvalis.ProjectiveSignFiltration

/-! Public interface for the actual Conway–Wales lattice construction. -/
namespace Atlas.Sporadic.Rudvalis
open Atlas.Rudvalis

/-- The full Gaussian automorphism group of the explicit lattice, modulo its scalar units. -/
noncomputable abbrev Model := RudvalisGroup
noncomputable abbrev LinearCover := gaussianLatticeGroup
noncomputable abbrev FrameGroup := projectiveFrameGroup
abbrev Points := MinimalCross
noncomputable abbrev Frames := canonicalBases
noncomputable def lattice : Submodule ℤ RationalSpace := rudvalisLattice
noncomputable def projection : LinearCover →* Model := QuotientGroup.mk' gaussianScalarSubgroup
noncomputable def frameEmbedding : ProjectiveCodeGroup →* Model := projectiveCodeHom
noncomputable def reflection : Model := projectiveReflection

theorem finite : Finite Model := inferInstance

theorem card : Nat.card Model=145926144000 := rudvalisGroup_order

theorem order : Nat.card Model=2^14*3^3*5^3*7*13*29 := by rw [card]; norm_num

theorem linear_card : Nat.card LinearCover=583704576000 := full_gaussian_order

theorem isSimpleGroup : IsSimpleGroup Model := rudvalis_simple

theorem nonabelian : ¬IsMulCommutative Model := rudvalis_nonabelian

theorem exists_mul_ne_mul : ∃g h : Model,g*h≠h*g := rudvalis_noncommutative

theorem faithful : FaithfulSMul Model Points := rudvalis_cross_faithful

theorem primitive : MulAction.IsPreprimitive Model Points := rudvalis_cross_primitive

theorem point_card : Nat.card Points=4060 := rudvalisLattice_minimal_cross_card

theorem frame_card : Nat.card Frames=424125 := canonicalBases_card

theorem frame_group_card : Nat.card FrameGroup=344064 := projectiveFrameGroup_order

theorem frame_group_perfect : Group.IsPerfect FrameGroup := projectiveFrameGroup_perfect

theorem point_stabilizer_card (x : Points) : Nat.card (MulAction.stabilizer Model x)=35942400 :=
  rudvalis_point_stabilizer_order x

theorem projection_surjective : Function.Surjective projection := QuotientGroup.mk'_surjective _

theorem projection_kernel : projection.ker=gaussianScalarSubgroup := QuotientGroup.ker_mk' _

theorem frameEmbedding_injective : Function.Injective frameEmbedding := projectiveCodeHom_injective

theorem reflection_square : reflection^2=1 := projectiveReflection_square

theorem generation : projectiveFrameGroup ⊔ Subgroup.zpowers reflection=⊤ :=
  projectiveFrameGroup_reflection_generate

theorem center : Subgroup.center LinearCover=gaussianScalarSubgroup := full_gaussian_center_eq_scalars

theorem center_card : Nat.card (Subgroup.center LinearCover)=4 := by
  rw [center,gaussianScalarSubgroup_card]

noncomputable def frameLinearMap : ProjectiveCodeGroup →* (E ≃ₗ[Bit] E) := projectiveCodeBlockHom

theorem frameLinearMap_surjective : Function.Surjective frameLinearMap := projectiveCodeBlockHom_surjective

theorem frameLinearMap_kernel_card : Nat.card frameLinearMap.ker=2048 := projectiveCodeBlockHom_kernel_order

noncomputable def frameTranslationMap : projectiveRowKernel →* Multiplicative ProjectiveTranslationModule :=
  projectiveRowMatrixHom

theorem frameTranslationMap_surjective : Function.Surjective frameTranslationMap := projectiveRowMatrixHom_surjective

theorem frameTranslationMap_kernel : frameTranslationMap.ker=projectiveSignKernel := projectiveRowMatrixHom_kernel_eq_signs

theorem frameTranslation_dimension : Module.finrank Bit ProjectiveTranslationModule=8 := projectiveTranslationModule_finrank

theorem frameSigns_dimension : Module.finrank Bit (Additive projectiveSignKernel)=3 := projectiveSignKernel_finrank

end Atlas.Sporadic.Rudvalis

