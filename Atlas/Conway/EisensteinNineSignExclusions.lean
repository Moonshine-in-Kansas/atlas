import Atlas.Conway.EisensteinNineOtherDisjoint
import Atlas.Conway.EisensteinNineSignWitnesses

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

attribute [local instance] eisensteinNineSignPhaseAction

theorem eisensteinNineSignFrame_not_unit (b : ZMod 3) (F : EisensteinFrame)
    (hF : EisensteinNineSignFrame b F) : F ∉ eisensteinUnitResidueFrames := by
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,rfl⟩ := hF
  rw [eisensteinFrame_unitResidue_iff]
  have hr : eisensteinResidue (x.val.val 0)=0 := by
    rw [hx]
    change eisensteinResidue (eisensteinTheta * eisensteinConstantNineForm s k b z t 0)=0
    simp [show eisensteinResidue eisensteinTheta=0 by decide +kernel]
  exact fun h => h hr

theorem eisensteinNineSignFrame_not_balancedNine (b : ZMod 3) (F : EisensteinFrame)
    (hF : EisensteinNineSignFrame b F) : F ∉ eisensteinBalancedNineFamily := by
  intro hG
  obtain ⟨y,hy,hyfull⟩ := eisensteinBalancedFamilies_full F (Or.inr hG)
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,hxF⟩ := hF
  apply eisensteinConstantBalanced_frame_ne y x hyfull
    ⟨eisensteinConstantNineForm s k b z t,s,hx,eisensteinConstantNineForm_wordResidue s k b z t⟩
  exact hy.trans hxF.symm

/-- Any intrinsic nonzero constant-nine sign excludes all eleven other local
families, independently of the choice of support and phase representatives. -/
theorem eisensteinNineSignFrame_not_other (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : EisensteinNineSignFrame b F)
    (i : Fin 13) (h3 : i≠3) (h4 : i≠4) : F ∉ eisensteinSuborbitFrames i := by
  by_cases hd : 243 ∣ eisensteinSubdegree i
  · by_cases h12 : i=12
    · subst i
      exact eisensteinNineSignFrame_not_balancedNine b F hF
    · have hi : i=5 ∨ i=6 ∨ i=7 ∨ i=9 ∨ i=10 ∨ i=11 := eisensteinSubdegree_divisible243_indices i h3 h4 h12 hd
      intro hmem
      exact eisensteinNineSignFrame_not_unit b F hF (eisensteinUnitSuborbit_subset i hi hmem)
  · obtain ⟨G,hG⟩ := eisensteinElevenSuborbit_orbit i h3 h4
    rw [hG]
    apply eisenstein_phase243_not_mem_local_orbit F G
      (eisensteinNineSignFrame_phase_orbit_card b hb F hF)
    rw [← hG,eisensteinSuborbitFrames_card]
    exact hd

end Atlas.Conway
