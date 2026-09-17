import Atlas.Fischer.ParkerRayRepresentation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The literal conjugation-set stabilizer of the actual standard frame. -/
def standardFrameRayStabilizer : Subgroup rootGeneratedRayGroup :=
  Subgroup.normalizer standardCommutingFrame

theorem parkerRayHom_mem_frame (h : ParkerStandardGroup) :
    parkerRayHom h ∈ standardFrameRayStabilizer := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  apply Set.Subset.antisymm
  · rintro x ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨(parkerStandardProjection h).val i,(parkerRayHom_conjugate_basic h i).symm⟩
  · rintro x ⟨i,rfl⟩
    refine ⟨distinguishedRootElement (.inl ((parkerStandardProjection h).val.symm i)),⟨_,rfl⟩,?_⟩
    rw [show MulAut.conj (parkerRayHom h) (distinguishedRootElement (.inl _))=
      parkerRayHom h * distinguishedRootElement (.inl _) * (parkerRayHom h)⁻¹ from rfl,
      parkerRayHom_conjugate_basic,Equiv.apply_symm_apply]

theorem parkerRayHom_range : parkerRayHom.range=standardFrameRayStabilizer := by
  apply le_antisymm
  · rintro x ⟨h,rfl⟩
    exact parkerRayHom_mem_frame h
  · intro g hg
    obtain ⟨e,he⟩ := fullSemilinearRayProjection_surjective g
    have hec : semilinearGeneratedConjugation e=MulAut.conj g := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      change semilinearDisplayedRayAction e=g.val at he'
      change semilinearDisplayedRayAction e*x.val*(semilinearDisplayedRayAction e)⁻¹=
        g.val*x.val*g.val⁻¹
      rw [he']
    have hf : e ∈ basicFrameStabilizer := by
      apply semilinear_mem_basicFrame_of_class_image
      rw [hec,(Subgroup.mem_normalizer_iff_conj_image_eq.mp hg)]
    obtain ⟨a,h,hh⟩ := (mem_basicFrameStabilizer_iff_scalar_parker e).mp hf
    refine ⟨h,?_⟩
    have ha : fullSemilinearRayProjection (scalarAlgebraRepresentation a)=1 := by
      change scalarAlgebraRepresentation a ∈ fullSemilinearRayProjection.ker
      rw [fullSemilinearRayProjection_kernel]
      exact ⟨a,rfl⟩
    rw [hh,map_mul,ha,one_mul] at he
    exact he

/-- The actual standard-frame stabilizer is isomorphic to the retained Parker
group through its faithful ray representation. -/
def parkerStandardFrameEquiv : ParkerStandardGroup ≃* standardFrameRayStabilizer :=
  (MonoidHom.ofInjective parkerRayHom_injective).trans
    (MulEquiv.subgroupCongr parkerRayHom_range)

end Atlas.Fischer
