import Atlas.LinearGroups.Triality.RankOneBruhat

/-! The parabolics are literally obtained by adjoining the corresponding
negative root group to B; together they generate the actual matrix group. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem shortRoot_mem_borel (t : K) : shortRoot F K t ∈ borel F K hdeg := by
  apply unipotent_le_borel F K hdeg
  exact ⟨⟨t,0,0,0,0,0⟩, positiveMatrix_short F K t⟩

theorem shortParabolic_eq_negative :
    shortParabolic F K hdeg = borel F K hdeg ⊔ Subgroup.closure (Set.range (shortNegativeRoot F K)) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    have hr : shortRoot F K 1 ∈ borel F K hdeg ⊔ Subgroup.closure (Set.range (shortNegativeRoot F K)) :=
      (le_sup_left : borel F K hdeg ≤ _) (shortRoot_mem_borel F K hdeg 1)
    have hn : shortNegativeRoot F K (-1) ∈ borel F K hdeg ⊔ Subgroup.closure (Set.range (shortNegativeRoot F K)) :=
      (le_sup_right : Subgroup.closure (Set.range (shortNegativeRoot F K)) ≤ _)
        (Subgroup.subset_closure ⟨-1,rfl⟩)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hn) hr
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact shortNegativeRoot_mem_parabolic F K hdeg t

theorem longRoot_mem_borel (t : F) : longRoot F K t ∈ borel F K hdeg := by
  apply unipotent_le_borel F K hdeg
  exact ⟨⟨0,t,0,0,0,0⟩, positiveMatrix_long F K t⟩

theorem longParabolic_eq_negative :
    longParabolic F K hdeg = borel F K hdeg ⊔ Subgroup.closure (Set.range (longNegativeRoot F K)) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    have hr : longRoot F K 1 ∈ borel F K hdeg ⊔ Subgroup.closure (Set.range (longNegativeRoot F K)) :=
      (le_sup_left : borel F K hdeg ≤ _) (longRoot_mem_borel F K hdeg 1)
    have hn : longNegativeRoot F K (-1) ∈ borel F K hdeg ⊔ Subgroup.closure (Set.range (longNegativeRoot F K)) :=
      (le_sup_right : Subgroup.closure (Set.range (longNegativeRoot F K)) ≤ _)
        (Subgroup.subset_closure ⟨-1,rfl⟩)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hn) hr
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact longNegativeRoot_mem_parabolic F K hdeg t

theorem parabolic_sup_eq_generated :
    shortParabolic F K hdeg ⊔ longParabolic F K hdeg = generated F K := by
  apply le_antisymm (sup_le (shortParabolic_le_generated F K hdeg) (longParabolic_le_generated F K hdeg))
  apply (Subgroup.closure_le _).mpr
  have hb : borel F K hdeg ≤ shortParabolic F K hdeg ⊔ longParabolic F K hdeg :=
    le_trans (le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) le_sup_left
  rintro g (((⟨a,rfl⟩ | ⟨a,rfl⟩) | ⟨b,rfl⟩) | ⟨b,rfl⟩)
  · exact hb (shortRoot_mem_borel F K hdeg a)
  · exact (le_sup_left : shortParabolic F K hdeg ≤ _) (shortNegativeRoot_mem_parabolic F K hdeg a)
  · exact hb (longRoot_mem_borel F K hdeg b)
  · exact (le_sup_right : longParabolic F K hdeg ≤ _) (longNegativeRoot_mem_parabolic F K hdeg b)

end Atlas.Triality
