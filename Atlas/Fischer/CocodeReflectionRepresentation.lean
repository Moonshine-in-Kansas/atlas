import Atlas.Fischer.BasicCocodeComparison
import Atlas.Fischer.CocodeInvolutions
import Atlas.Fischer.ParkerCoordinateFaithfulness

namespace Atlas.Fischer
open Atlas.Codes

/-- The actual faithful action of the retained cocode on the coordinate algebra. -/
noncomputable def cocodeCoordinateRepresentation : Multiplicative Cocode →* Equiv.Perm Coordinates :=
  (MulAction.toPermHom ParkerStandardGroup Coordinates).comp parkerCocodeEmbedding

theorem cocodeCoordinateRepresentation_injective : Function.Injective cocodeCoordinateRepresentation := by
  intro d e h
  apply parkerCocodeEmbedding_injective
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Coordinates)
  intro x
  exact congrArg (fun p : Equiv.Perm Coordinates => p x) h

theorem cocodeCoordinateRepresentation_apply (d : Multiplicative Cocode) (x : Coordinates) :
    cocodeCoordinateRepresentation d x = parkerCoordinateAction (parkerCocodeEmbedding d) x := rfl

theorem cocodeCoordinateRepresentation_generator (i : Omega) (x : Coordinates) :
    cocodeCoordinateRepresentation (cocodeInvolution i) x = rootMap (basicAxis i) x := by
  rw [cocodeCoordinateRepresentation_apply]
  have he : parkerCocodeEmbedding (cocodeInvolution i) =
      parkerCocodeStandard (coordinateCocode i) := rfl
  rw [he]
  exact (rootMap_basicAxis_eq_cocode i x).symm

/-- The exact source relation statement, now for the represented operators. -/
theorem cocodeReflection_relations (S : Finset Omega) :
    cocodeCoordinateRepresentation (∏ i ∈ S, cocodeInvolution i) = 1 ↔
      binarySupportEquiv.symm S ∈ golay := by
  rw [← cocodeCoordinateRepresentation.map_one,
    cocodeCoordinateRepresentation_injective.eq_iff, cocodeInvolutions_relation]

private theorem permutation_involutive_of_square {α : Type*} (p : Equiv.Perm α)
    (h : p ^ 2 = 1) : Function.Involutive p := by
  intro x
  have hh : p * p = 1 := by simpa only [pow_two] using h
  exact congrArg (fun q : Equiv.Perm α => q x) hh

theorem basicAxis_rootMap_involutive (i : Omega) : Function.Involutive (rootMap (basicAxis i)) := by
  have he : (fun x => cocodeCoordinateRepresentation (cocodeInvolution i) x) =
      rootMap (basicAxis i) := funext (cocodeCoordinateRepresentation_generator i)
  rw [← he]
  apply permutation_involutive_of_square
  rw [← map_pow, cocodeInvolution_square, map_one]

theorem basicAxis_rootMap_order (i : Omega) :
    orderOf (cocodeCoordinateRepresentation (cocodeInvolution i)) = 2 := by
  rw [orderOf_injective _ cocodeCoordinateRepresentation_injective, cocodeInvolution_order]

noncomputable def cocodeReflectionRangeEquiv :
    Multiplicative Cocode ≃* cocodeCoordinateRepresentation.range :=
  MonoidHom.ofInjective cocodeCoordinateRepresentation_injective

theorem cocodeReflectionGroup_order : Nat.card cocodeCoordinateRepresentation.range = 4096 := by
  rw [← Nat.card_congr cocodeReflectionRangeEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative Cocode ≃ Cocode), cocode_card]

theorem cocodeReflections_generate :
    Subgroup.closure (Set.range (fun i => cocodeCoordinateRepresentation (cocodeInvolution i))) =
      cocodeCoordinateRepresentation.range := by
  have hs : Set.range (fun i => cocodeCoordinateRepresentation (cocodeInvolution i)) =
      cocodeCoordinateRepresentation '' Set.range cocodeInvolution := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨cocodeInvolution i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨d, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hs, ← MonoidHom.map_closure, cocodeInvolutions_generate,
    ← MonoidHom.range_eq_map]

end Atlas.Fischer
