import Atlas.Conway.EisensteinHexadNormalization
import Atlas.Conway.EisensteinHexadPhaseCoordinateNorms
import Atlas.Lattices.EisensteinFrameVectorMembership

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- An arbitrary normalized constant-heavy short vector determines an actual phased heavy frame. -/
theorem eisensteinHexad_normalized_frame (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k : Fin 12) (hk : k ∈ s)
    (x : EisensteinShell 6) (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u)
    (hr : eisensteinWordResidue u=ternaryTriadWord s)
    (hn : ∀ i,(u i).norm=if i=k then 4 else if i ∈ s then 1 else 0) :
    ∃ a : ternaryGolay,eisensteinFrameOfVector x=
      eisensteinPhaseIsometries (Multiplicative.ofAdd a) • eisensteinHexadFrame s hs k hk := by
  obtain ⟨a,ha⟩ := eisensteinHexad_normalized_code_phase s hs k hk u hr hn (hu ▸ x.val.property)
  refine ⟨a,?_⟩
  rw [eisensteinHexadFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val=(eisensteinIntegralAction _ _).val
  rw [eisensteinIntegralAction_phase,hu]
  exact ha

/-- No short frame containing a coordinate of scalar norm nine can contain a
normalized constant-heavy vector. This applies to every representative of the frame. -/
theorem eisensteinHexad_normalized_excludes_nine (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k : Fin 12) (hk : k ∈ s)
    (x y : EisensteinShell 6) (u : EisensteinCoordinates) (hu : y.val.val=eisensteinTheta • u)
    (hr : eisensteinWordResidue u=ternaryTriadWord s)
    (hn : ∀ i,(u i).norm=if i=k then 4 else if i ∈ s then 1 else 0)
    (hf : eisensteinFrameOfVector x=eisensteinFrameOfVector y) (j : Fin 12)
    (hj : (x.val.val j).norm=9) : False := by
  obtain ⟨a,ha⟩ := eisensteinHexad_normalized_frame s hs k hk y u hu hr hn
  rw [ha] at hf
  have hx := (eisensteinFrameOfVector_eq_iff_mem x _).mp hf
  have h := eisensteinHexadPhaseFrame_coordinate_norms s hs k hk a x hx j
  rcases h with h|h|h <;> omega

end Atlas.Conway
