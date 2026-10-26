import Atlas.LinearGroups.Triality.BruhatClosure

/-! Every element of the generated triality matrix group lies in one of its
 twelve concrete Borel double cells. No order or simplicity theorem is used. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Atlas.GroupTheory
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem bruhat_exhaustion (g : O_DPlus 4 K) (hg : g ∈ generated F K) :
    ∃ w : Fin 12, ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg,
      g = b * weylLift F K w * c := by
  let S : Set (O_DPlus 4 K) := {g | BruhatCellUnion F K hdeg g}
  have hb : borel F K hdeg ≤ leftPreservers S := by
    intro a ha x hx
    exact bruhat_mul_left F K hdeg ha hx
  have hs : shortWeyl F K ∈ leftPreservers S := by
    intro x hx
    exact shortWeyl_bruhat_closed F K hdeg hx
  have hl : longWeyl F K ∈ leftPreservers S := by
    intro x hx
    exact longWeyl_bruhat_closed F K hdeg hx
  have hgen : generated F K ≤ leftPreservers S := by
    rw [← parabolic_sup_eq_generated F K hdeg]
    apply sup_le
    · exact sup_le hb ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hs))
    · exact sup_le hb ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hl))
  apply mem_of_leftPreservers (S := S) _ (hgen hg)
  exact ⟨0,1,Subgroup.one_mem _,1,Subgroup.one_mem _,by simp [weylLift,weylWord]⟩

theorem generated_mem_iff_bruhat (g : O_DPlus 4 K) :
    g ∈ generated F K ↔ BruhatCellUnion F K hdeg g := by
  constructor
  · exact bruhat_exhaustion F K hdeg g
  · rintro ⟨w,b,hb,c,hc,rfl⟩
    have hw : weylLift F K w ∈ generated F K := by
      apply weylSubgroup_le_generated F K hdeg
      exact ⟨(w,1),by simp [weylTorusWord]⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (borel_le_generated F K hdeg hb) hw)
      (borel_le_generated F K hdeg hc)

end Atlas.Triality
