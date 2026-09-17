import Atlas.Conway.EisensteinHexadRecognizedFrames
import Atlas.Lattices.EisensteinConstantNormPattern

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- Every positively normalized constant-hexad representative of a frame containing
norm nine has the same norm-nine/hexad pattern; the heavy-twelve alternative is impossible. -/
theorem eisenstein_constant_frame_norm9_pattern (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (x y : EisensteinShell 6)
    (u : EisensteinCoordinates) (hu : y.val.val=eisensteinTheta • u)
    (hr : eisensteinWordResidue u=ternaryTriadWord s)
    (hf : eisensteinFrameOfVector x=eisensteinFrameOfVector y)
    (j : Fin 12) (hj : (x.val.val j).norm=9) :
    ∃ k : Fin 12,k ∉ s ∧ ∀ i,(u i).norm=(if i ∈ s then 1 else 0)+(if i=k then 3 else 0) := by
  obtain ⟨k,hk⟩ := eisenstein_constant_normalized_norm_pattern s
    ((mem_ternaryConstantHexads _).mp hs).1 y u hu hr
  refine ⟨k,?_,hk⟩
  intro hks
  apply eisensteinHexad_normalized_excludes_nine s hs k hks x y u hu hr _ hf j hj
  intro i
  rw [hk]
  by_cases hi : i=k
  · subst i; simp [hks]
  · simp [hi]

end Atlas.Conway
