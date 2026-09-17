import Atlas.Conway.EisensteinUnitResidueExhaustion
import Atlas.Lattices.EisensteinClassZeroResidue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def eisensteinUnitResidueFrames : Set EisensteinFrame :=
  ((((eisensteinHeavyUnitFrames ∪ eisensteinPairUnitFrames false) ∪ eisensteinPairUnitFrames true) ∪
    eisensteinTriadUnitFrames 0) ∪ eisensteinTriadUnitFrames 1) ∪ eisensteinTriadUnitFrames 2

private theorem card_union {α : Type*} [Finite α] (S T : Set α) (h : Disjoint S T) :
    Nat.card (S ∪ T : Set α)=Nat.card S+Nat.card T := by
  rw [Nat.card_congr (Equiv.Set.union h),Nat.card_sum]

theorem eisensteinUnitResidueFrames_card : Nat.card eisensteinUnitResidueFrames=155277 := by
  have h01 : Disjoint (eisensteinTriadUnitFrames 0) (eisensteinTriadUnitFrames 1) :=
    eisensteinTriadUnitFrames_disjoint 0 1 (by decide)
  have h02 : Disjoint (eisensteinTriadUnitFrames 0) (eisensteinTriadUnitFrames 2) :=
    eisensteinTriadUnitFrames_disjoint 0 2 (by decide)
  have h12 : Disjoint (eisensteinTriadUnitFrames 1) (eisensteinTriadUnitFrames 2) :=
    eisensteinTriadUnitFrames_disjoint 1 2 (by decide)
  unfold eisensteinUnitResidueFrames
  rw [card_union _ _ (by simp only [Set.disjoint_union_left]; exact
    ⟨⟨⟨⟨eisensteinHeavy_triad_disjoint 2,eisensteinPair_triad_disjoint false 2⟩,
      eisensteinPair_triad_disjoint true 2⟩,h02⟩,h12⟩)]
  rw [card_union _ _ (by simp only [Set.disjoint_union_left]; exact
    ⟨⟨⟨eisensteinHeavy_triad_disjoint 1,eisensteinPair_triad_disjoint false 1⟩,
      eisensteinPair_triad_disjoint true 1⟩,h01⟩)]
  rw [card_union _ _ (by simp only [Set.disjoint_union_left]; exact
    ⟨⟨eisensteinHeavy_triad_disjoint 0,eisensteinPair_triad_disjoint false 0⟩,
      eisensteinPair_triad_disjoint true 0⟩)]
  rw [card_union _ _ (by simp only [Set.disjoint_union_left]; exact
    ⟨eisensteinHeavy_pair_disjoint true,eisensteinPairUnitFrames_disjoint⟩)]
  rw [card_union _ _ (eisensteinHeavy_pair_disjoint false)]
  rw [eisensteinHeavyUnitFrames_card,eisensteinPairUnitFrames_card,eisensteinPairUnitFrames_card,
    eisensteinTriadUnitFrames_card,eisensteinTriadUnitFrames_card,eisensteinTriadUnitFrames_card]

theorem eisensteinUnitResidueFrames_mem (F : EisensteinFrame) :
    F ∈ eisensteinUnitResidueFrames ↔ F ∈ eisensteinHeavyUnitFrames ∨
      (∃ b, F ∈ eisensteinPairUnitFrames b) ∨ ∃ r, F ∈ eisensteinTriadUnitFrames r := by
  simp only [eisensteinUnitResidueFrames,Set.mem_union,Bool.exists_bool,Fin.exists_fin_succ,
    Fin.exists_fin_zero,or_false]
  tauto

theorem eisensteinNonzeroResidue_mem (x : EisensteinShell 6)
    (hx : eisensteinResidue (x.val.val 0)≠0) : eisensteinFrameOfVector x ∈ eisensteinUnitResidueFrames :=
  (eisensteinUnitResidueFrames_mem _).mpr (eisensteinNonzeroResidue_frame_exhaust x hx)

theorem eisensteinFrame_residue_zero_iff (x y : EisensteinShell 6)
    (h : eisensteinFrameOfVector x=eisensteinFrameOfVector y) (j : Fin 12) :
    eisensteinResidue (x.val.val j)=0 ↔ eisensteinResidue (y.val.val j)=0 := by
  rcases (eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val h) with hc|hc
  · rw [eisensteinClass_coordinateResidue x.val y.val hc j]
  · rw [← map_neg] at hc
    have he := eisensteinClass_coordinateResidue x.val (-y.val) hc j
    change eisensteinResidue (x.val.val j)=eisensteinResidue (-y.val.val j) at he
    rw [he,map_neg,neg_eq_zero]

theorem eisensteinUnitResidueFrames_iff (F : EisensteinFrame) :
    F ∈ eisensteinUnitResidueFrames ↔
      ∃ x : EisensteinShell 6, eisensteinResidue (x.val.val 0)≠0 ∧ eisensteinFrameOfVector x=F := by
  constructor
  · intro h
    rcases (eisensteinUnitResidueFrames_mem F).mp h with ⟨⟨i,t⟩,rfl⟩|⟨b,⟨⟨p,t⟩,rfl⟩⟩|⟨r,⟨⟨e,t⟩,rfl⟩⟩
    · refine ⟨eisensteinCodePhaseShell t (eisensteinHeavyUnitVector i),?_,rfl⟩
      rw [eisensteinOneModThree_phase_residue _ ⟨Pi.single i 1,fun _ => rfl⟩]
      decide
    · refine ⟨eisensteinCodePhaseShell t (eisensteinPairUnitVector b p),?_,rfl⟩
      rw [eisensteinOneModThree_phase_residue _ (eisensteinPairUnit_oneModThree b p)]
      decide
    · refine ⟨eisensteinCodePhaseShell t (eisensteinTriadUnitVector r e),?_,rfl⟩
      rw [eisensteinOneModThree_phase_residue _ (eisensteinTriadUnit_oneModThree r e)]
      decide
  · rintro ⟨x,hx,rfl⟩
    exact eisensteinNonzeroResidue_mem x hx

theorem eisensteinFrame_unitResidue_iff (x : EisensteinShell 6) :
    eisensteinFrameOfVector x ∈ eisensteinUnitResidueFrames ↔ eisensteinResidue (x.val.val 0)≠0 := by
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := (eisensteinUnitResidueFrames_iff _).mp h
    exact fun hx => hy ((eisensteinFrame_residue_zero_iff x y he.symm 0).mp hx)
  · exact eisensteinNonzeroResidue_mem x

theorem eisensteinZeroResidueFrames_card : Nat.card (eisensteinUnitResidueFramesᶜ : Set EisensteinFrame)=77683 := by
  have h := Nat.card_congr (Equiv.Set.sumCompl eisensteinUnitResidueFrames)
  rw [Nat.card_sum,eisensteinUnitResidueFrames_card,eisensteinFrame_card] at h
  omega

end Atlas.Conway
