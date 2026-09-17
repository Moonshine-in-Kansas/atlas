import Atlas.Fischer.ResidueModels
import Atlas.Fischer.CoordinateCocodeSpans

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def residueCocodeSubgroup (S : Finset Omega) : Subgroup (Multiplicative Cocode) :=
  (coordinateCocodeSpan S).toAddSubgroup.toSubgroup

theorem generatedCocodeRayHom_coordinate (i : Omega) :
    generatedCocodeRayHom (Multiplicative.ofAdd (coordinateCocode i)) = distinguishedRootElement (.inl i) := by
  apply Subtype.ext
  exact cocodeRayHom_basic i

theorem residueElementary_eq_cocode_image (S : Finset Omega) :
    residueElementary S = (residueCocodeSubgroup S).map generatedCocodeRayHom := by
  have hs : ∀ d ∈ coordinateCocodeSpan S,
      generatedCocodeRayHom (Multiplicative.ofAdd d) ∈ residueElementary S := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨i,hi,rfl⟩ := hd
      rw [generatedCocodeRayHom_coordinate]
      exact Subgroup.subset_closure ⟨i,hi,rfl⟩
    | zero =>
      change generatedCocodeRayHom 1 ∈ _
      rw [map_one]
      exact (residueElementary S).one_mem
    | add d e hd he ihd ihe =>
      change generatedCocodeRayHom (Multiplicative.ofAdd d * Multiplicative.ofAdd e) ∈ _
      rw [map_mul]
      exact (residueElementary S).mul_mem ihd ihe
    | smul a d hd ih =>
      fin_cases a
      · change generatedCocodeRayHom (Multiplicative.ofAdd ((0 : Bit) • d)) ∈ _
        rw [zero_smul]
        change generatedCocodeRayHom 1 ∈ _
        rw [map_one]
        exact (residueElementary S).one_mem
      · change generatedCocodeRayHom (Multiplicative.ofAdd ((1 : Bit) • d)) ∈ _
        rw [one_smul]
        exact ih
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,hi,rfl⟩
    exact ⟨Multiplicative.ofAdd (coordinateCocode i),
      (show coordinateCocode i ∈ coordinateCocodeSpan S from Submodule.subset_span ⟨i,hi,rfl⟩),generatedCocodeRayHom_coordinate i⟩
  · rintro x ⟨d,hd,rfl⟩
    exact hs d.toAdd hd

theorem generatedCocodeRayHom_mem_residueElementary (S : Finset Omega) (d : Multiplicative Cocode) :
    generatedCocodeRayHom d ∈ residueElementary S ↔ d.toAdd ∈ coordinateCocodeSpan S := by
  rw [residueElementary_eq_cocode_image]
  constructor
  · rintro ⟨e,he,hed⟩
    have h : e=d := cocodeRayHom_injective (congrArg Subtype.val hed)
    exact h ▸ he
  · intro hd
    exact ⟨d,hd,rfl⟩

end Atlas.Fischer
