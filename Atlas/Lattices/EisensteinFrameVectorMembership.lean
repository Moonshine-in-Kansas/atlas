import Atlas.Lattices.EisensteinFrameVectors

namespace Atlas.Lattices
noncomputable section

theorem eisensteinFrameOfVector_eq_iff_mem (x : EisensteinShell 6) (F : EisensteinFrame) :
    eisensteinFrameOfVector x=F ↔ x ∈ eisensteinFrameVectors F := by
  classical
  constructor
  · intro h
    rw [← h]
    simp [eisensteinFrameVectors,eisensteinFrameOfVector,eisensteinFramePair]
  · intro hx
    obtain ⟨c,hc,hF⟩ := eisensteinFrame_pair F
    apply Subtype.ext
    change eisensteinFramePair (eisensteinClass x.val)=F.val
    rw [hF,eisensteinFramePair_eq_iff]
    have hh := (Finset.mem_filter.mp hx).2
    rw [hF] at hh
    simpa [eisensteinFramePair] using hh

end
end Atlas.Lattices
