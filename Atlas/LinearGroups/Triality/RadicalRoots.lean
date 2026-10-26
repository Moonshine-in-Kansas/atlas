import Atlas.LinearGroups.Triality.Radicals

/-! Root subgroups inside the concrete simple-coordinate kernels. -/
noncomputable section
namespace Atlas.Triality
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem longRoot_mem_shortRadical (t : F) : longRoot F K t ∈ shortRadical F K hdeg := by
  apply (shortRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,t,0,0,0,0⟩, rfl, positiveMatrix_long F K t⟩

theorem nextShortRoot_mem_shortRadical (t : K) : nextShortRoot F K t ∈ shortRadical F K hdeg := by
  apply (shortRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,t,0,0,0⟩, rfl, positiveMatrix_next F K t⟩

theorem middleRoot_mem_shortRadical (t : K) : middleRoot F K t ∈ shortRadical F K hdeg := by
  apply (shortRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,0,t,0,0⟩, rfl, positiveMatrix_middle F K t⟩

theorem highLongRoot_mem_shortRadical (t : F) : highLongRoot F K t ∈ shortRadical F K hdeg := by
  apply (shortRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,0,0,t,0⟩, rfl, positiveMatrix_high F K t⟩

theorem highestRoot_mem_shortRadical (t : F) : highestRoot F K t ∈ shortRadical F K hdeg := by
  apply (shortRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,0,0,0,t⟩, rfl, positiveMatrix_highest F K t⟩

theorem shortRoot_mem_longRadical (t : K) : shortRoot F K t ∈ longRadical F K hdeg := by
  apply (longRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨t,0,0,0,0,0⟩, rfl, positiveMatrix_short F K t⟩

theorem nextShortRoot_mem_longRadical (t : K) : nextShortRoot F K t ∈ longRadical F K hdeg := by
  apply (longRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,t,0,0,0⟩, rfl, positiveMatrix_next F K t⟩

theorem middleRoot_mem_longRadical (t : K) : middleRoot F K t ∈ longRadical F K hdeg := by
  apply (longRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,0,t,0,0⟩, rfl, positiveMatrix_middle F K t⟩

theorem highLongRoot_mem_longRadical (t : F) : highLongRoot F K t ∈ longRadical F K hdeg := by
  apply (longRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,0,0,t,0⟩, rfl, positiveMatrix_high F K t⟩

theorem highestRoot_mem_longRadical (t : F) : highestRoot F K t ∈ longRadical F K hdeg := by
  apply (longRadical_mem_iff F K hdeg _).mpr
  exact ⟨⟨0,0,0,0,0,t⟩, rfl, positiveMatrix_highest F K t⟩

end Atlas.Triality
