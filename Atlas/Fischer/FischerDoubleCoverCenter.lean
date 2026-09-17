import Atlas.Fischer.FischerDoubleCoverPerfect
import Atlas.Fischer.ResidueSimplicity
import Atlas.GroupTheory.CenterKernel
import Atlas.Algebra.PerfectCentralNonsplit

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem doubleCover_center (i j : Omega) (hij : i≠j) :
    Subgroup.center (FischerDoubleCover i j)=Subgroup.zpowers (doubleCoverMarkedElement i j j) := by
  have hS : ({i,j}:Finset Omega).card=2 := by simp [hij]
  letI := residueGroup_simple ({i,j}:Finset Omega) (by omega) (by omega)
  have hc : Subgroup.center (ResidueGroup {i,j})=⊥ := by
    rcases (inferInstance : (Subgroup.center (ResidueGroup {i,j})).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (residueGroup_noncommutative {i,j} (by omega) (by omega)
        (Subgroup.center_eq_top_iff.mp h)).elim
  rw [← doubleCoverProjection_kernel i j hij]
  exact Atlas.GroupTheory.center_eq_kernel_of_surjective (doubleCoverProjection i j)
    (doubleCoverProjection_surjective i j) hc (doubleCoverProjection_kernel_central i j)

/-- Nonsplitting refers to the actual double-centralizer quotient map. -/
theorem doubleCoverProjection_nonsplit (i j : Omega) (hij : i≠j) :
    ¬ ∃ s : ResidueGroup {i,j} →* FischerDoubleCover i j,
      (doubleCoverProjection i j).comp s=MonoidHom.id _ := by
  rintro ⟨s,hs⟩
  letI := doubleCover_perfect i j hij
  have h := Atlas.Algebra.perfect_central_section_kernel_eq_bot (doubleCoverProjection i j)
    (doubleCoverProjection_kernel_central i j) s hs
  have hc := doubleCoverProjection_kernel_card i j hij
  rw [h,Subgroup.card_bot] at hc
  omega

end Atlas.Fischer
