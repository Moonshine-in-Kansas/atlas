import Atlas.GroupTheory.ThreeTranspositionFrames

namespace Atlas.GroupTheory

/-- An automorphism preserving the distinguished set transports its maximal
commuting subsets. No finiteness or transitivity hypothesis is used. -/
theorem IsCommutingFrame.image {G : Type*} [Group G] {D F : Set G}
    (hF : IsCommutingFrame D F) (e : MulAut G) (hD : e '' D=D) :
    IsCommutingFrame D (e '' F) := by
  have hforward {x : G} (hx : x ∈ D) : e x ∈ D := by
    rw [← hD]
    exact ⟨x,hx,rfl⟩
  have hback {x : G} (hx : x ∈ D) : e.symm x ∈ D := by
    rw [← hD] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa using hy
  refine ⟨?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact hforward (hF.1 hy)
  · rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    exact (hF.2.1 a ha b hb).map e.toMonoidHom
  · intro E hE hc hsub
    have heq : e.symm '' E=F := hF.2.2 _ (by
      rintro x ⟨y,hy,rfl⟩
      exact hback (hE hy)) (by
      rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
      exact (hc a ha b hb).map e.symm.toMonoidHom) (by
      intro x hx
      exact ⟨e x,hsub ⟨x,hx,rfl⟩,e.symm_apply_apply x⟩)
    apply Set.Subset.antisymm ?_ hsub
    intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    rw [← heq]
    exact ⟨x,hx,rfl⟩

end Atlas.GroupTheory
