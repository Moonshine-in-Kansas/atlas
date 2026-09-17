import Atlas.Fischer.RootRayCovariance

noncomputable section
namespace Atlas.Fischer

/-- Every full semilinear algebra automorphism conjugates generated ray
permutations back into the actual root-generated group. -/
theorem semilinear_ray_conjugate_mem (e : SemilinearAlgebraAutomorphism)
    (g : Equiv.Perm DisplayedReflectingRay) (hg : g ∈ rootGeneratedRayGroup) :
    semilinearDisplayedRayAction e * g * (semilinearDisplayedRayAction e)⁻¹ ∈
      rootGeneratedRayGroup := by
  have hle : rootGeneratedRayGroup.map (MulAut.conj (semilinearDisplayedRayAction e)) ≤
      rootGeneratedRayGroup := by
    change (Subgroup.closure (Set.range displayedRootRayInvolution)).map _ ≤ _
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
    obtain ⟨s,hs⟩ := reflectingRootParameter_automorphism e t
    change semilinearDisplayedRayAction e * displayedRootRayInvolution t *
      (semilinearDisplayedRayAction e)⁻¹ ∈ rootGeneratedRayGroup
    rw [displayedRootRayInvolution_covariance e t s hs]
    exact displayedRootRayInvolution_mem s
  exact hle ⟨g,hg,rfl⟩

theorem semilinear_ray_mem_normalizer (e : SemilinearAlgebraAutomorphism) :
    semilinearDisplayedRayAction e ∈ Subgroup.normalizer (rootGeneratedRayGroup :
      Set (Equiv.Perm DisplayedReflectingRay)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact semilinear_ray_conjugate_mem e g
  · intro hg
    have h := semilinear_ray_conjugate_mem e⁻¹ _ hg
    simpa only [map_inv,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using h

/-- The full inverse image of the actual generated ray group, before proving
that it equals all semilinear automorphisms. -/
def generatedRayPreimage : Subgroup SemilinearAlgebraAutomorphism :=
  rootGeneratedRayGroup.comap semilinearDisplayedRayAction

instance generatedRayPreimageNormal : generatedRayPreimage.Normal where
  conj_mem g hg e := by
    change semilinearDisplayedRayAction (e*g*e⁻¹) ∈ rootGeneratedRayGroup
    rw [map_mul,map_mul,map_inv]
    exact semilinear_ray_conjugate_mem e _ hg

end Atlas.Fischer
