import Atlas.Fischer.RootRaySeparation
import Mathlib.GroupTheory.Subgroup.Center

noncomputable section
namespace Atlas.Fischer

/-- The actual distinguished involution as an element of the root-generated group. -/
def distinguishedRootElement (t : ReflectingRootParameter) : rootGeneratedRayGroup :=
  ⟨displayedRootRayInvolution t,displayedRootRayInvolution_mem t⟩

def DistinguishedRootClass := Set.range distinguishedRootElement

theorem distinguishedRootElement_injective : Function.Injective distinguishedRootElement := by
  intro i j h
  exact displayedRootRayInvolution_injective (congrArg Subtype.val h)

/-- The actual normalized rays identify bijectively with the distinguished
involutions, after the independent separation proof. -/
def displayedRayDistinguishedEquiv : DisplayedReflectingRay ≃ DistinguishedRootClass :=
  (Equiv.ofBijective displayedRayOfParameter
    ⟨fun _ _ h => reflectingRootParameterRay_injective (congrArg Subtype.val h),
      displayedRayOfParameter_surjective⟩).symm.trans
    (Equiv.ofInjective distinguishedRootElement distinguishedRootElement_injective)

theorem distinguishedRootClass_card : Nat.card DistinguishedRootClass=306936 := by
  rw [← Nat.card_congr displayedRayDistinguishedEquiv]
  exact displayedReflectingRay_card

/-- Commuting with every distinguished involution forces an actual ray
permutation to be the identity. -/
theorem rootGeneratedRayGroup_central_eq_one (g : rootGeneratedRayGroup)
    (hc : ∀ i, g.val * displayedRootRayInvolution i=displayedRootRayInvolution i * g.val) : g=1 := by
  obtain ⟨e,he⟩ := rootGeneratedRayGroup_lift g
  apply Subtype.ext
  apply Equiv.ext
  intro R
  obtain ⟨i,rfl⟩ := displayedRayOfParameter_surjective R
  obtain ⟨t,ht⟩ := reflectingRootParameter_automorphism e.val i
  have hd := displayedRootRayInvolution_covariance e.val i t ht
  rw [he] at hd
  have hsame : displayedRootRayInvolution i=displayedRootRayInvolution t := by
    calc
      _ = g.val * displayedRootRayInvolution i * g.val⁻¹ := by rw [hc i,mul_assoc,mul_inv_cancel,mul_one]
      _ = _ := hd
  have hti : i=t := displayedRootRayInvolution_injective hsame
  apply Subtype.ext
  rw [← he,semilinearDisplayedRayAction_parameter_value,ht,← hti]
  rfl

theorem rootGeneratedRayGroup_center : Subgroup.center rootGeneratedRayGroup=⊥ := by
  apply le_antisymm
  · intro g hg
    change g=1
    apply rootGeneratedRayGroup_central_eq_one
    intro i
    have hc := (Subgroup.mem_center_iff.mp hg) (distinguishedRootElement i)
    exact (congrArg Subtype.val hc).symm
  · exact bot_le

end Atlas.Fischer
