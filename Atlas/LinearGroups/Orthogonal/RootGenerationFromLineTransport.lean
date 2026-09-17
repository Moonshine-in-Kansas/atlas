import Atlas.LinearGroups.Orthogonal.RootSubgroupConjugation

/-! # Elementary generation from an actual subgroup's singular-line transport -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem elementary_le_of_root_and_line_transport (Q : QuadraticForm F V)
    (H : Subgroup (isometrySubgroup Q)) (e : V) (he : Q e = 0)
    (hr : rootSubgroup Q e he ≤ H)
    (ht : ∀ u : V, u ≠ 0 → Q u = 0 →
      ∃ g : isometrySubgroup Q, g ∈ H ∧ ∃ c : F, c ≠ 0 ∧ g.val e = c • u) :
    elementarySubgroup Q ≤ H := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨u,v,hu,huv,rfl⟩
  by_cases hun : u = 0
  · subst u
    have hid : siegelElement Q 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change Atlas.Quadratic.siegel Q 0 v x = x
      simp [Atlas.Quadratic.siegel]
    rw [hid]
    exact H.one_mem
  · obtain ⟨g,hg,c,hc,hgu⟩ := ht u hun hu
    have hroot : (rootSubgroup Q e he).map (MulAut.conj g) = rootSubgroup Q u hu := by
      rw [rootSubgroup_conj]
      simpa only [hgu] using rootSubgroup_scale Q u hu c hc
    have hx : siegelElement Q u v hu huv ∈ (rootSubgroup Q e he).map (MulAut.conj g) := by
      rw [hroot]
      exact ⟨Multiplicative.ofAdd ⟨v,huv⟩,rfl⟩
    obtain ⟨r,hr',hrr⟩ := hx
    rw [← hrr]
    exact H.mul_mem (H.mul_mem hg (hr hr')) (H.inv_mem hg)

end Atlas.Orthogonal
