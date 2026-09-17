import Atlas.Fischer.GeneratedRootGroups
import Atlas.Fischer.CocodeReflectionRepresentation
import Atlas.Fischer.ParkerAlgebraRepresentation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The retained cocode inside the actual semilinear algebra group. -/
def cocodeAlgebraHom : Multiplicative Cocode →* SemilinearAlgebraAutomorphism :=
  parkerAlgebraRepresentation.comp parkerCocodeEmbedding

theorem cocodeAlgebraHom_apply (d : Multiplicative Cocode) (x : Coordinates) :
    (cocodeAlgebraHom d).val x=parkerCoordinateAction (parkerCocodeEmbedding d) x := rfl

theorem cocodeAlgebraHom_injective : Function.Injective cocodeAlgebraHom :=
  parkerAlgebraRepresentation_injective.comp parkerCocodeEmbedding_injective

theorem cocodeAlgebraHom_basic (i : Omega) :
    cocodeAlgebraHom (cocodeInvolution i)=displayedRootAutomorphism (.inl i) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simp only [displayedRootAutomorphism,reflectingRootAutomorphism_apply,
    reflectingRootParameterVector]
  rw [cocodeAlgebraHom_apply,← cocodeCoordinateRepresentation_apply]
  exact cocodeCoordinateRepresentation_generator i x

/-- The cocode is proved to lie in the root-generated group through its
basic generators; it is not inserted into the generating set. -/
theorem cocodeAlgebraHom_range_le : cocodeAlgebraHom.range ≤ rootGeneratedAlgebraGroup := by
  rw [MonoidHom.range_eq_map, ← cocodeInvolutions_generate, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  rw [cocodeAlgebraHom_basic]
  exact displayedRootAutomorphism_mem (.inl i)

theorem cocodeAlgebraHom_mem (d : Multiplicative Cocode) :
    cocodeAlgebraHom d ∈ rootGeneratedAlgebraGroup :=
  cocodeAlgebraHom_range_le ⟨d,rfl⟩

theorem cocodeAlgebraHom_relations (S : Finset Omega) :
    cocodeAlgebraHom (∏ i ∈ S, cocodeInvolution i)=1 ↔
      binarySupportEquiv.symm S ∈ golay := by
  rw [← cocodeAlgebraHom.map_one,cocodeAlgebraHom_injective.eq_iff,
    cocodeInvolutions_relation]

theorem cocodeAlgebraHom_range_card : Nat.card cocodeAlgebraHom.range=4096 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective cocodeAlgebraHom_injective).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative Cocode ≃ Cocode),cocode_card]

end Atlas.Fischer
