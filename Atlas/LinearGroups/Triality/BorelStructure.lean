import Atlas.LinearGroups.Triality.Borel

/-! Internal product and normalization interfaces for the actual Borel subgroup. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem unipotent_le_borel (hdeg : Module.finrank F K = 3) :
    unipotent F K hdeg ≤ borel F K hdeg := by
  rintro _ ⟨p,rfl⟩
  exact ⟨(p,1),by simp [borelWord]⟩

theorem torus_le_borel (hdeg : Module.finrank F K = 3) :
    torus F K ≤ borel F K hdeg := by
  rintro _ ⟨h,rfl⟩
  exact ⟨(⟨0,0,0,0,0,0⟩,h),by simp [borelWord,positiveMatrix_zero]⟩

theorem borel_eq_sup (hdeg : Module.finrank F K = 3) :
    borel F K hdeg = unipotent F K hdeg ⊔ torus F K := by
  apply le_antisymm
  · rintro _ ⟨⟨p,h⟩,rfl⟩
    have hU : unipotent F K hdeg ≤ unipotent F K hdeg ⊔ torus F K := le_sup_left
    have hH : torus F K ≤ unipotent F K hdeg ⊔ torus F K := le_sup_right
    exact Subgroup.mul_mem _ (hU ⟨p,rfl⟩) (hH ⟨h,rfl⟩)
  · exact sup_le (unipotent_le_borel F K hdeg) (torus_le_borel F K hdeg)

set_option maxHeartbeats 1000000 in
-- Elaborate the two concrete subgroup coordinate witnesses.
theorem unipotent_inf_torus (hdeg : Module.finrank F K = 3) :
    unipotent F K hdeg ⊓ torus F K = ⊥ := by
  apply bot_unique
  rintro g ⟨⟨p,hp⟩,⟨h,hh⟩⟩
  have he : borelWord F K p 1 = borelWord F K ⟨0,0,0,0,0,0⟩ h := by
    simpa [borelWord,positiveMatrix_zero] using hp.trans hh.symm
  have hi : (p,(1 : Kˣ × Fˣ)) = (⟨0,0,0,0,0,0⟩,h) := borelWord_injective F K he
  have ht : (1 : Kˣ × Fˣ) = h := congrArg Prod.snd hi
  rw [Subgroup.mem_bot,←hh,←ht,map_one]

theorem torus_normalizes_unipotent (hdeg : Module.finrank F K = 3) :
    torus F K ≤ Subgroup.normalizer (unipotent F K hdeg : Set (O_DPlus 4 K)) := by
  rintro _ ⟨h,rfl⟩
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨p,rfl⟩
  refine ⟨torusScale F K h p, ?_⟩
  rw [torus_positive_intertwine F K hdeg]
  group

end Atlas.Triality
