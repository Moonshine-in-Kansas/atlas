import Atlas.Fischer.DuadCharacterDecomposition
import Atlas.Fischer.DuadCocode
import Atlas.Fischer.OctadShortenedDivisibility

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual weight-eight/sixteen labels span the shortened duad code. -/
theorem duadCoordinateWord_span (p : Finset Omega) (hp : p.card=2) :
    Submodule.span Bit (Set.range (fun c : DuadCoordinateWord p => c.val))=⊤ := by
  let W := Submodule.span Bit (Set.range (fun c : DuadCoordinateWord p => c.val))
  have hshort (O : Octad) (hO : p ⊆ O.val) (c : octadShortenedCode O) :
      (⟨c.val,octadShortenedCode_le_duad p O hO c.property⟩ : duadShortenedCode p) ∈ W := by
    rcases octadShortened_weights O c with hz | h8 | h16
    · have he : c.val=0 := Subtype.ext (hammingNorm_eq_zero.mp hz)
      have hc : (⟨c.val,octadShortenedCode_le_duad p O hO c.property⟩ : duadShortenedCode p)=0 :=
        Subtype.ext he
      rw [hc]
      exact W.zero_mem
    · apply Submodule.subset_span
      exact ⟨⟨⟨c.val,octadShortenedCode_le_duad p O hO c.property⟩,Or.inl h8⟩,rfl⟩
    · apply Submodule.subset_span
      exact ⟨⟨⟨c.val,octadShortenedCode_le_duad p O hO c.property⟩,Or.inr h16⟩,rfl⟩
  obtain ⟨F,G,hFG⟩ := duad_octad_pair_exists p hp
  apply Submodule.eq_top_iff'.mpr
  intro c
  obtain ⟨⟨x,y⟩,rfl⟩ := (duadOctadSumEquiv p hp F G hFG).surjective c
  exact W.add_mem (hshort F (hFG ▸ Finset.inter_subset_left) x)
    (hshort G (hFG ▸ Finset.inter_subset_right) y)

/-- Characters are determined on the actual coordinate-label set. -/
theorem duadCharacter_ext_coordinates (p : Finset Omega) (hp : p.card=2)
    (χ ψ : Module.Dual Bit (duadShortenedCode p))
    (h : ∀ c : DuadCoordinateWord p, χ c.val=ψ c.val) : χ=ψ :=
  LinearMap.ext_on_range (duadCoordinateWord_span p hp) h

end Atlas.Fischer
