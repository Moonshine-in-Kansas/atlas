import Atlas.GroupTheory.CommutingFrameExtension
import Atlas.Fischer.CommutingFrameConjugacy

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every finite ordered commuting tuple of distinct distinguished elements can
be conjugated into the actual marked basic frame. -/
theorem commutingTuple_into_standard {s : ℕ} (t : Fin s ↪ rootGeneratedRayGroup)
    (ht : ∀ k, t k ∈ Set.range distinguishedRootElement)
    (hc : ∀ k l, Commute (t k) (t l)) :
    ∃ g : rootGeneratedRayGroup, ∃ a : Fin s ↪ Omega,
      ∀ k, g * t k * g⁻¹ = distinguishedRootElement (.inl (a k)) := by
  classical
  obtain ⟨F,hF,hsub⟩ := Atlas.GroupTheory.exists_commutingFrame_containing
    (Set.range distinguishedRootElement) (Set.range t)
    (by rintro x ⟨k,rfl⟩; exact ht k)
    (by rintro x ⟨k,rfl⟩ y ⟨l,rfl⟩; exact hc k l)
  obtain ⟨g,hg⟩ := fischerFrames_conjugate F standardCommutingFrame hF
    standardCommutingFrame_isFrame
  have hm (k : Fin s) : g * t k * g⁻¹ ∈ standardCommutingFrame := by
    rw [← hg]
    exact ⟨t k,hsub ⟨k,rfl⟩,rfl⟩
  choose a ha using hm
  have hi : Function.Injective a := by
    intro k l h
    apply t.injective
    apply (MulAut.conj g).injective
    exact (ha k).symm.trans ((congrArg (fun i => distinguishedRootElement (.inl i)) h).trans (ha l))
  exact ⟨g,⟨a,hi⟩,fun k => (ha k).symm⟩

end Atlas.Fischer
