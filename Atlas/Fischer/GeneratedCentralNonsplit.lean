import Atlas.Fischer.GeneratedCentralExtension
import Atlas.Algebra.PerfectCentralNonsplit

namespace Atlas.Fischer

/-- The central triple extension of the actual positive ray group does not
split: a section would contradict perfectness and its nontrivial scalar kernel. -/
theorem rootGeneratedPositiveProjection_nonsplit :
    ¬ ∃ s : rootGeneratedRayParity.ker →* rootGeneratedAlgebraParity.ker,
      rootGeneratedPositiveProjection.comp s=MonoidHom.id _ := by
  rintro ⟨s,hs⟩
  letI := rootGeneratedAlgebraParity_kernel_perfect
  have h := Atlas.Algebra.perfect_central_section_kernel_eq_bot
    rootGeneratedPositiveProjection rootGeneratedPositiveProjection_kernel_central s hs
  have hc := rootGeneratedPositiveProjection_kernel_card
  rw [h,Subgroup.card_bot] at hc
  norm_num at hc

end Atlas.Fischer
