import Atlas.Rudvalis.ProjectiveFrameFiltration
import Atlas.Rudvalis.ProjectivePrimitivity
import Atlas.GroupTheory.CenterSimpleQuotient
import Atlas.Rudvalis.ProjectiveFrameEmbedding
import Atlas.Rudvalis.FrameLinearSimplicity
import Atlas.Rudvalis.FrameTranslationCommutators
import Atlas.GroupTheory.PrimitivePerfectFrameSimplicity

namespace Atlas.Rudvalis

/-- Actual frame-group embedding transports the verified perfectness theorem. -/
theorem projectiveFrameGroup_perfect : Group.IsPerfect projectiveFrameGroup := by
  let := projectiveCodeGroup_perfect
  exact Group.IsPerfect.ofSurjective projectiveFrameEquiv.surjective

/-- Application of the normal-subgroup criterion with the actual quotient,
frame subgroup, reflection and already verified orders. -/
theorem rudvalis_simple_of_primitive_frame_quotient
    (hprimitive : MulAction.IsPreprimitive RudvalisGroup MinimalCross)
    (π : ProjectiveCodeGroup →* (E ≃ₗ[Bit] E))
    (hπ : Function.Surjective π) [Group.IsSolvable π.ker] : IsSimpleGroup RudvalisGroup := by
  let : Nontrivial RudvalisGroup := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [rudvalisGroup_order];decide)
  let := hprimitive
  let := rudvalis_cross_faithful
  let := projectiveFrameGroup_perfect
  let := binaryLinearGroup_simple
  let f : projectiveFrameGroup →* (E ≃ₗ[Bit] E) :=
    π.comp projectiveFrameEquiv.symm.toMonoidHom
  have hf : Function.Surjective f := hπ.comp projectiveFrameEquiv.symm.surjective
  let e : f.ker →* π.ker :=
    { toFun := fun g => ⟨projectiveFrameEquiv.symm g.val,g.prop⟩
      map_one' := Subtype.ext (map_one projectiveFrameEquiv.symm)
      map_mul' := fun a b => Subtype.ext (map_mul projectiveFrameEquiv.symm a.val b.val) }
  have he : Function.Injective e := by
    intro a b h
    exact Subtype.ext (projectiveFrameEquiv.symm.injective (congrArg Subtype.val h))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective he
  have hp : 7 ∣ Nat.card (E ≃ₗ[Bit] E) := by rw [binaryLinearGroup_order];decide
  have hx : ¬7 ∣ Nat.card (MulAction.stabilizer RudvalisGroup localReferenceCross) := by
    rw [rudvalis_point_stabilizer_order];decide
  have ho : Odd projectiveFrameGroup.index := by
    rw [projectiveFrameGroup_index]
    exact ⟨212062,by decide⟩
  exact Atlas.GroupTheory.simple_of_primitive_perfect_frame projectiveFrameGroup f hf 7 hp
    localReferenceCross hx ho projectiveReflection projectiveReflection_square
    projectiveFrameGroup_reflection_generate


/-- Simplicity of the actual full Gaussian lattice group modulo its four scalar units. -/
theorem rudvalis_simple : IsSimpleGroup RudvalisGroup := by
  let := projectiveCodeBlockHom_kernel_solvable
  exact rudvalis_simple_of_primitive_frame_quotient rudvalis_cross_primitive
    projectiveCodeBlockHom projectiveCodeBlockHom_surjective

theorem rudvalis_nonabelian : ¬IsMulCommutative RudvalisGroup := by
  intro h
  let := rudvalis_simple
  let : CommGroup RudvalisGroup := Group.commGroupOfCenterEqTop (Subgroup.center_eq_top_iff.mpr h)
  have hp := IsSimpleGroup.prime_card (α := RudvalisGroup)
  rw [rudvalisGroup_order] at hp
  have hd : 2 ∣ 145926144000 := ⟨72963072000,rfl⟩
  have he := (Nat.dvd_prime hp).mp hd
  norm_num at he

theorem rudvalis_noncommutative : ∃g h : RudvalisGroup,g*h≠h*g := by
  classical
  simpa only [isMulCommutative_iff,not_forall] using rudvalis_nonabelian

theorem full_gaussian_center_eq_scalars :
    Subgroup.center gaussianLatticeGroup=gaussianScalarSubgroup := by
  let := rudvalis_simple
  exact Atlas.GroupTheory.center_eq_of_simple_quotient gaussianLatticeGroup
    gaussianScalarSubgroup gaussianScalarSubgroup_le_center rudvalis_nonabelian

theorem rudvalis_center_eq_bot : Subgroup.center RudvalisGroup=⊥ := by
  let := rudvalis_simple
  exact Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian RudvalisGroup rudvalis_nonabelian

end Atlas.Rudvalis
