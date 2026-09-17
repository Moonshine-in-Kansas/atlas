import Atlas.Conway.EisensteinConstantNineSignSum
import Atlas.Lattices.EisensteinThetaFrameDifference

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem eisensteinConstantNineForm_residue (s : Finset (Fin 12)) (k : Fin 12)
    (b z : ZMod 3) (t : TernaryWord) (i : Fin 12) :
    eisensteinResidue (eisensteinConstantNineForm s k b z t i)=if i ∈ s then 1 else 0 := by
  by_cases hi : i ∈ s <;> by_cases hik : i=k <;>
    simp [eisensteinConstantNineForm,hi,hik,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel]
  all_goals split_ifs <;> simp only [eisensteinPhase_residue,map_zero]

/-- The correction sign is invariant under intrinsic frame equivalence with fixed positive hexad. -/
theorem eisensteinConstantNine_frame_sign_same (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k l : Fin 12) (hk : k ∉ s) (hl : l ∉ s)
    (b d z w : ZMod 3) (t v : TernaryWord) (ht : (∑ i ∈ s,t i)=b) (hv : (∑ i ∈ s,v i)=d)
    (hU : eisensteinTheta • eisensteinConstantNineForm s k b z t ∈ eisensteinLeechModule)
    (hV : eisensteinTheta • eisensteinConstantNineForm s l d w v ∈ eisensteinLeechModule)
    (he : eisensteinFramePair (eisensteinClass ⟨_,hU⟩)=eisensteinFramePair (eisensteinClass ⟨_,hV⟩)) :
    b=d := by
  rcases eisensteinTheta_frame_difference _ _ hU hV he with h|h
  · exact eisensteinConstantNine_sign_sub s hs k l hk hl b d z w t v ht hv h
  · obtain ⟨i,hi⟩ := Finset.card_pos.mp
      (show 0<s.card by rw [((mem_ternaryConstantHexads s).mp hs).1]; decide)
    have hr := eisensteinLeech_residue_coordinates _ h i k
    simp only [Pi.add_apply,map_add,eisensteinConstantNineForm_residue,hi,hk,ite_true,ite_false,
      zero_add] at hr
    exact (by decide : (1 : ZMod 3)+1≠0) hr |>.elim

/-- The same correction sign is preserved when the positive support is replaced by its complement. -/
theorem eisensteinConstantNine_frame_sign_compl (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k l : Fin 12) (hk : k ∉ s) (hl : l ∈ s)
    (b d z w : ZMod 3) (t v : TernaryWord) (ht : (∑ i ∈ s,t i)=b)
    (hU : eisensteinTheta • eisensteinConstantNineForm s k b z t ∈ eisensteinLeechModule)
    (hV : eisensteinTheta • eisensteinConstantNineForm sᶜ l d w v ∈ eisensteinLeechModule)
    (he : eisensteinFramePair (eisensteinClass ⟨_,hU⟩)=eisensteinFramePair (eisensteinClass ⟨_,hV⟩)) :
    b=d := by
  rcases eisensteinTheta_frame_difference _ _ hU hV he with h|h
  · have hr := eisensteinLeech_residue_coordinates _ h l k
    simp only [Pi.sub_apply,map_sub,eisensteinConstantNineForm_residue,Finset.mem_compl,
      hl,hk,not_true_eq_false,not_false_eq_true,ite_true,ite_false,sub_zero,zero_sub] at hr
    exact (by decide : (1 : ZMod 3)≠ -1) hr |>.elim
  · exact eisensteinConstantNine_sign_add_compl s hs k l hk hl b d z w t v ht h

end Atlas.Conway
