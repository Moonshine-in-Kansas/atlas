import Atlas.Fischer.FischerRayPrimitivity
import Atlas.Fischer.FischerAssociatedOrders
import Atlas.GroupTheory.PrimitiveIndexTwoSimplicity

noncomputable section
namespace Atlas.Fischer

/-- The positive actual ray group is simple by the primitive involution-class argument. -/
theorem rootGeneratedRayPositive_simple : IsSimpleGroup rootGeneratedRayParity.ker := by
  haveI := rootGeneratedRayGroup_primitive
  have hcard : Nat.card (commutator rootGeneratedRayGroup)=1255205709190661721292800 := by
    rw [rootGeneratedRay_commutator]
    exact rootGeneratedRayPositive_order
  haveI : Nontrivial (commutator rootGeneratedRayGroup) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let t : DisplayedReflectingRay → rootGeneratedRayGroup :=
    fun R => (displayedRayDistinguishedEquiv R).val
  have ht : Function.Injective t := fun x y h =>
    displayedRayDistinguishedEquiv.injective (Subtype.ext h)
  have hr : Set.range t=Set.range distinguishedRootElement := by
    ext g
    constructor
    · rintro ⟨R,rfl⟩
      exact (displayedRayDistinguishedEquiv R).property
    · intro hg
      obtain ⟨R,hR⟩ := displayedRayDistinguishedEquiv.surjective ⟨g,hg⟩
      exact ⟨R,congrArg Subtype.val hR⟩
  let i : Atlas.Codes.Omega := ((0,0),0)
  let x := displayedRayOfParameter (.inl i)
  have hs : t x*t x=1 := by
    change (displayedRayDistinguishedEquiv x).val * (displayedRayDistinguishedEquiv x).val=1
    rw [displayedRayDistinguishedEquiv_parameter]
    have h := orderOf_dvd_iff_pow_eq_one.mp
      (show orderOf (distinguishedRootElement (.inl i)) ∣ 2 by rw [distinguishedRootElement_order])
    simpa only [pow_two] using h
  have hsimple := Atlas.GroupTheory.simple_derived_of_primitive_involution_class t ht
    (fun g R => displayedRayDistinguishedEquiv_equivariant g R)
    (by rw [hr]; exact distinguishedRootClass_generates) x
    rootGeneratedRay_commutator_index hs
    (by rw [hcard,displayedReflectingRay_card]; decide)
  rw [rootGeneratedRay_commutator] at hsimple
  exact hsimple

theorem rootGeneratedRayPositive_noncommutative : ¬IsMulCommutative rootGeneratedRayParity.ker := by
  haveI : Nontrivial rootGeneratedRayParity.ker :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [rootGeneratedRayPositive_order]; decide)
  haveI := rootGeneratedRayParity_kernel_perfect
  exact Group.IsPerfect.not_isMulCommutative rootGeneratedRayParity.ker

end Atlas.Fischer
