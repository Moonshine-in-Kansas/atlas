import Atlas.Fischer.MarkedPentadFrameCount
import Atlas.Fischer.OctadicFrameConjugation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Both companions are reached by actual root involutions fixing the marked
pentad pointwise, with no ambient group-order or frame-transitivity premise. -/
theorem markedPentad_parity_switch (S : Finset Omega) (hS : S.card=5) (e : Bit) :
    ∃ g : rootGeneratedRayGroup,
      (∀ i ∈ S,(MulAut.conj g) (distinguishedRootElement (.inl i))=
        distinguishedRootElement (.inl i)) ∧
      (MulAut.conj g) '' standardCommutingFrame=
        octadicParityFrame (markedPentadOctad S hS) e := by
  let O := markedPentadOctad S hS
  obtain ⟨χ⟩ := octadicParityClass_nonempty O (e+1)
  refine ⟨distinguishedRootElement (.inr (.inl ⟨O,χ.val⟩)),?_,?_⟩
  · intro i hi
    exact octadicRoot_conjugation_inside O χ.val i (markedPentadOctad_contains S hS hi)
  · rw [octadicRoot_conjugation_frame,χ.prop]
    have he : e+1+1=e := by
      rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
    rw [he]

/-- The actual pointwise pentad stabilizer reaches every one of its three frames. -/
theorem markedPentadFrame_reachable (S : Finset Omega) (hS : S.card=5)
    (F : MarkedPentadFrame S) :
    ∃ g : rootGeneratedRayGroup,
      (∀ i ∈ S,(MulAut.conj g) (distinguishedRootElement (.inl i))=
        distinguishedRootElement (.inl i)) ∧
      (MulAut.conj g) '' standardCommutingFrame=F.val := by
  rcases markedPentadFrame_classification S hS F with h | ⟨e,h⟩
  · refine ⟨1,?_,?_⟩
    · intro i hi; simp
    · simpa using h.symm
  · obtain ⟨g,hg,hf⟩ := markedPentad_parity_switch S hS e
    exact ⟨g,hg,hf.trans h.symm⟩

end Atlas.Fischer
