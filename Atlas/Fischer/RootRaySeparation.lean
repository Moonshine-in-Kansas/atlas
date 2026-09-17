import Atlas.Fischer.RootRayProductOrders
import Atlas.Fischer.BasicSupportSeparation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem displayedRootRayInvolution_eq_basic_iff (t : ReflectingRootParameter) (i : Omega) :
    displayedRootRayInvolution t=displayedRootRayInvolution (.inl i) ↔ t=.inl i := by
  constructor
  · intro he
    have hfull : ∀ j, hermitian (basicAxis j) (reflectingRootParameterVector t) ≠ 0 := by
      intro j hz
      have hf : displayedRootRayInvolution (.inl i) (displayedRayOfParameter (.inl j)) =
          displayedRayOfParameter (.inl j) := by
        apply (displayedRootRayInvolution_fixed_iff _ _).mpr
        change hermitian (basicAxis i) (basicAxis j) ≠ 0
        rw [hermitian_basicAxis_basicAxis]
        split_ifs <;> norm_num
      rw [← he] at hf
      have hn := (displayedRootRayInvolution_fixed_iff t (.inl j)).mp hf
      apply hn
      change hermitian (reflectingRootParameterVector t) (basicAxis j)=0
      rw [← hermitian_star,hz,star_zero]
    obtain ⟨j,rfl⟩ := displayedRoot_full_basic_support t hfull
    have hij : j=i := by
      by_contra hn
      obtain ⟨a,hj,hi⟩ := basic_axes_separated_by_octadic j i hn
      have hf : displayedRootRayInvolution (.inl j) (displayedRayOfParameter (.inr (.inl a))) =
          displayedRayOfParameter (.inr (.inl a)) := by
        apply (displayedRootRayInvolution_fixed_iff _ _).mpr
        change hermitian (basicAxis j) (octadicRoot (chosenOctadCalibration a.1) a.2) ≠ 0
        rw [hj]
        exact one_ne_zero
      rw [he] at hf
      exact ((displayedRootRayInvolution_fixed_iff _ _).mp hf) hi
    subst j
    rfl
  · rintro rfl
    rfl

/-- Conjugation carries any distinguished generator to any other, using only
zero-graph transitivity and actual algebra covariance. -/
theorem displayedRootRayInvolution_conjugate (i j : ReflectingRootParameter) :
    ∃ g : rootGeneratedRayGroup,
      g.val * displayedRootRayInvolution i * g.val⁻¹=displayedRootRayInvolution j := by
  obtain ⟨g,hg⟩ := rootGeneratedRayGroup_parameter_transitive i j
  obtain ⟨e,he⟩ := rootGeneratedRayGroup_lift g
  refine ⟨g,?_⟩
  rw [← he]
  apply displayedRootRayInvolution_covariance
  have hv := congrArg Subtype.val hg
  rw [← he,semilinearDisplayedRayAction_parameter_value] at hv
  exact hv

/-- Basic separation transported by the actual generated group proves global
injection of rays into the distinguished involutions. -/
theorem displayedRootRayInvolution_injective : Function.Injective displayedRootRayInvolution := by
  intro i j hij
  let k : Omega := Classical.arbitrary Omega
  obtain ⟨g,hg⟩ := rootGeneratedRayGroup_parameter_transitive i (.inl k)
  obtain ⟨e,he⟩ := rootGeneratedRayGroup_lift g
  have hi : rootRay (e.val.val (reflectingRootParameterVector i))=reflectingRootParameterRay (.inl k) := by
    have hv := congrArg Subtype.val hg
    rw [← he,semilinearDisplayedRayAction_parameter_value] at hv
    exact hv
  obtain ⟨t,ht⟩ := reflectingRootParameter_automorphism e.val j
  have hc := displayedRootRayInvolution_covariance e.val i (.inl k) hi
  have hd := displayedRootRayInvolution_covariance e.val j t ht
  rw [hij] at hc
  have htk : t=.inl k := (displayedRootRayInvolution_eq_basic_iff t k).mp (hd.symm.trans hc)
  have hj : g.val (displayedRayOfParameter j)=displayedRayOfParameter (.inl k) := by
    apply Subtype.ext
    rw [← he,semilinearDisplayedRayAction_parameter_value,ht,htk]
    rfl
  exact reflectingRootParameterRay_injective
    (congrArg Subtype.val (g.val.injective (hg.trans hj.symm)))

/-- Distinct nonzero-pairing rays give an exact order-two product. -/
theorem displayedRootRay_nonzero_product_order (i j : ReflectingRootParameter) (hij : i ≠ j)
    (hn : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0) :
    orderOf (displayedRootRayInvolution i * displayedRootRayInvolution j)=2 := by
  have hc : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)^3=1 := by
    rcases reflectingRoot_pairing_zero_or_mu3 _ _ (reflectingRootParameter_isReflectingRoot i)
      (reflectingRootParameter_isReflectingRoot j) (reflectingRootParameter_distinct_phases i j hij)
      with hz | ⟨a,ha⟩
    · exact (hn hz).elim
    · rw [ha]
      exact (mem_rootsOfUnity' _ _).mp a.property
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime (displayedRootRay_unit_product_square i j hc)
  intro he
  have heq := inv_eq_of_mul_eq_one_right he
  rw [displayedRootRayInvolution_inv] at heq
  exact hij (displayedRootRayInvolution_injective heq)

end Atlas.Fischer
