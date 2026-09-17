import Atlas.Fischer.RootRayClass
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Conj

noncomputable section
namespace Atlas.Fischer

@[simp] theorem displayedRayDistinguishedEquiv_parameter (i : ReflectingRootParameter) :
    (displayedRayDistinguishedEquiv (displayedRayOfParameter i)).val=distinguishedRootElement i := by
  let e := Equiv.ofBijective displayedRayOfParameter
    ⟨fun _ _ h => reflectingRootParameterRay_injective (congrArg Subtype.val h),
      displayedRayOfParameter_surjective⟩
  change ((Equiv.ofInjective distinguishedRootElement distinguishedRootElement_injective)
    (e.symm (e i))).val=distinguishedRootElement i
  rw [Equiv.symm_apply_apply]
  rfl

theorem distinguishedRootElement_conjugation (g : rootGeneratedRayGroup)
    (i j : ReflectingRootParameter) (hg : g.val (displayedRayOfParameter i)=displayedRayOfParameter j) :
    g * distinguishedRootElement i * g⁻¹=distinguishedRootElement j := by
  obtain ⟨e,he⟩ := rootGeneratedRayGroup_lift g
  apply Subtype.ext
  change g.val * displayedRootRayInvolution i * g.val⁻¹=displayedRootRayInvolution j
  rw [← he]
  apply displayedRootRayInvolution_covariance
  have hv := congrArg Subtype.val hg
  rw [← he,semilinearDisplayedRayAction_parameter_value] at hv
  exact hv

/-- The ray/class bijection intertwines the actual ray action with conjugation. -/
theorem displayedRayDistinguishedEquiv_equivariant (g : rootGeneratedRayGroup)
    (R : DisplayedReflectingRay) :
    (displayedRayDistinguishedEquiv (g.val R)).val =
      g * (displayedRayDistinguishedEquiv R).val * g⁻¹ := by
  obtain ⟨i,rfl⟩ := displayedRayOfParameter_surjective R
  obtain ⟨j,hj⟩ := displayedRayOfParameter_surjective (g.val (displayedRayOfParameter i))
  rw [← hj,displayedRayDistinguishedEquiv_parameter,displayedRayDistinguishedEquiv_parameter]
  exact (distinguishedRootElement_conjugation g i j hj.symm).symm

/-- The distinguished elements form one whole conjugacy class in the actual
root-generated group. -/
theorem distinguishedRootClass_isConj_iff (i : ReflectingRootParameter) (x : rootGeneratedRayGroup) :
    x ∈ Set.range distinguishedRootElement ↔ IsConj (distinguishedRootElement i) x := by
  constructor
  · rintro ⟨j,rfl⟩
    obtain ⟨g,hg⟩ := displayedRootRayInvolution_conjugate i j
    apply isConj_iff.mpr
    exact ⟨g,Subtype.ext hg⟩
  · intro hx
    obtain ⟨g,hg⟩ := isConj_iff.mp hx
    obtain ⟨j,hj⟩ := displayedRayOfParameter_surjective (g.val (displayedRayOfParameter i))
    exact ⟨j,(distinguishedRootElement_conjugation g i j hj.symm).symm.trans hg⟩

/-- No extra subgroup was inserted: these distinguished involutions generate
the entire actual root-generated ray group. -/
theorem distinguishedRootClass_generates :
    Subgroup.closure (Set.range distinguishedRootElement)=⊤ := by
  have he : Set.range distinguishedRootElement =
      rootGeneratedRayGroup.subtype ⁻¹' Set.range displayedRootRayInvolution := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,Subtype.ext hi⟩
  rw [he]
  exact Subgroup.closure_preimage_eq_top (Set.range displayedRootRayInvolution)

theorem distinguishedRootElement_order (i : ReflectingRootParameter) :
    orderOf (distinguishedRootElement i)=2 := by
  rw [← orderOf_injective rootGeneratedRayGroup.subtype rootGeneratedRayGroup.subtype_injective]
  exact displayedRootRayInvolution_order i

/-- The exact diagram convention: zero pairing gives order three, while
nonzero pairing of distinct rays gives order two. -/
theorem distinguishedRootElement_product_order (i j : ReflectingRootParameter) (hij : i ≠ j) :
    orderOf (distinguishedRootElement i * distinguishedRootElement j) =
      if hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0 then 3 else 2 := by
  classical
  rw [← orderOf_injective rootGeneratedRayGroup.subtype rootGeneratedRayGroup.subtype_injective]
  by_cases h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0
  · rw [if_pos h]
    exact displayedRootRay_zero_product_order i j h
  · rw [if_neg h]
    exact displayedRootRay_nonzero_product_order i j hij h

instance rootGeneratedRayGroupPretransitive :
    MulAction.IsPretransitive rootGeneratedRayGroup DisplayedReflectingRay where
  exists_smul_eq := rootGeneratedRayGroup_transitive

instance rootGeneratedRayGroupFaithful : FaithfulSMul rootGeneratedRayGroup DisplayedReflectingRay where
  eq_of_smul_eq_smul := fun {g h} he => rootGeneratedRayGroup_faithful g h he

end Atlas.Fischer

