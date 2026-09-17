import Atlas.Fischer.GeneratedCocode
import Atlas.Fischer.RayKernelScalarSubgroup

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The cocode action on the constructed ray family. -/
def cocodeRayHom : Multiplicative Cocode →* Equiv.Perm DisplayedReflectingRay :=
  semilinearDisplayedRayAction.comp cocodeAlgebraHom

theorem cocodeAlgebraHom_fixes_u (d : Multiplicative Cocode) (i : Omega) :
    (cocodeAlgebraHom d).val (u i)=u i := by
  change parkerCoordinateAction (parkerCocodeStandard d.toAdd) (u i)=u i
  rw [parkerCoordinateAction_u,parkerCocodeStandard_projection]
  rfl

theorem cocodeRayHom_injective : Function.Injective cocodeRayHom := by
  apply (injective_iff_map_eq_one cocodeRayHom).mpr
  intro d hd
  have hk : cocodeAlgebraHom d ∈ semilinearRayKernel := hd
  obtain ⟨a,ha⟩ := (mem_semilinearRayKernel_scalar_iff _).mp hk
  let i : Omega := Classical.arbitrary Omega
  have he := (ha (u i)).symm.trans (cocodeAlgebraHom_fixes_u d i)
  have h1 : (a.val.val : Scalar)=1 := by
    apply smul_left_injective Scalar (coordinateVector_ne_zero (.inl i))
    simpa only [u,one_smul] using he
  apply cocodeAlgebraHom_injective
  rw [map_one]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (cocodeAlgebraHom d).val x=x
  simpa only [h1,one_smul] using ha x

theorem cocodeRayHom_basic (i : Omega) :
    cocodeRayHom (cocodeInvolution i)=displayedRootRayInvolution (.inl i) := by
  change semilinearDisplayedRayAction (cocodeAlgebraHom _) = _
  rw [cocodeAlgebraHom_basic]
  rfl

theorem cocodeRayHom_range_le : cocodeRayHom.range ≤ rootGeneratedRayGroup := by
  rintro _ ⟨d,rfl⟩
  rw [← rootGeneratedAlgebraGroup_ray_image]
  exact ⟨cocodeAlgebraHom d,cocodeAlgebraHom_mem d,rfl⟩

theorem cocodeRayHom_relations (S : Finset Omega) :
    cocodeRayHom (∏ i ∈ S,cocodeInvolution i)=1 ↔ binarySupportEquiv.symm S ∈ golay := by
  rw [← cocodeRayHom.map_one,cocodeRayHom_injective.eq_iff,cocodeInvolutions_relation]

theorem cocodeRayHom_range_card : Nat.card cocodeRayHom.range=4096 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective cocodeRayHom_injective).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative Cocode ≃ Cocode),cocode_card]

end Atlas.Fischer
