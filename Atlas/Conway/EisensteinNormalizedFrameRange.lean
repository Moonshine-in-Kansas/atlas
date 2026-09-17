import Atlas.Conway.EisensteinBalancedNineFrameProfile
import Atlas.Lattices.EisensteinThetaClassResidue

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- A normalized coordinate word takes all three residue values. -/
def EisensteinNormalizedFull (x : EisensteinLattice) : Prop :=
  ∃ u : EisensteinCoordinates, x.val=eisensteinTheta • u ∧
    Function.Surjective (eisensteinWordResidue u)

theorem ternaryBalanced_surjective (c : TernaryBalancedWords) :
    Function.Surjective c.val.val := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(ternaryPositiveSupport c.val.val).card by rw [c.prop.1]; decide)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<(ternaryNegativeSupport c.val.val).card by rw [c.prop.2]; decide)
  have hz : ∃ k,c.val.val k=0 := by
    by_contra h
    have he : ternarySupport c.val.val=Finset.univ := by
      ext k
      simp only [ternarySupport,Finset.mem_filter,Finset.mem_univ,true_and]
      exact iff_true_intro (not_exists.mp h k)
    have hh := ternaryBalanced_weight c.val.val c.prop
    rw [← ternarySupport_card,he] at hh
    norm_num at hh
  obtain ⟨k,hk⟩ := hz
  intro a
  have ha : a=0 ∨ a=1 ∨ a=2 := by revert a; decide
  rcases ha with rfl|rfl|rfl
  · exact ⟨k,hk⟩
  · exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  · exact ⟨j,(Finset.mem_filter.mp hj).2⟩

theorem eisensteinNormalizedFull_class (x y : EisensteinLattice)
    (h : eisensteinClass x=eisensteinClass y) (hx : EisensteinNormalizedFull x)
    (v : EisensteinCoordinates) (hy : y.val=eisensteinTheta • v) :
    Function.Surjective (eisensteinWordResidue v) := by
  obtain ⟨u,hu,hs⟩ := hx
  have hum : eisensteinTheta • u ∈ eisensteinLeechModule := hu ▸ x.prop
  have hvm : eisensteinTheta • v ∈ eisensteinLeechModule := hy ▸ y.prop
  have he : eisensteinClass ⟨eisensteinTheta • u,hum⟩=
      eisensteinClass ⟨eisensteinTheta • v,hvm⟩ := by
    have hxv : x=⟨eisensteinTheta • u,hum⟩ := Subtype.ext hu
    have hyv : y=⟨eisensteinTheta • v,hvm⟩ := Subtype.ext hy
    rwa [← hxv,← hyv]
  obtain ⟨a,ha⟩ := eisensteinTheta_class_residue u v hum hvm he
  intro b
  obtain ⟨i,hi⟩ := hs (b+a)
  refine ⟨i,?_⟩
  have hh := ha i
  change eisensteinResidue (u i)=b+a at hi
  change eisensteinResidue (v i)=b
  rw [hi] at hh
  linear_combination -hh

theorem eisensteinNormalizedFull_neg (x : EisensteinLattice)
    (hx : EisensteinNormalizedFull x) : EisensteinNormalizedFull (-x) := by
  obtain ⟨u,hu,hs⟩ := hx
  refine ⟨-u,?_,?_⟩
  · change -x.val=eisensteinTheta • (-u)
    rw [hu,smul_neg]
  · intro a
    obtain ⟨i,hi⟩ := hs (-a)
    refine ⟨i,?_⟩
    change eisensteinResidue (-(u i))=a
    rw [map_neg,show eisensteinResidue (u i)= -a from hi,neg_neg]

theorem eisensteinNormalizedFull_frame (x y : EisensteinShell 6)
    (he : eisensteinFrameOfVector x=eisensteinFrameOfVector y)
    (hx : EisensteinNormalizedFull x.val) (v : EisensteinCoordinates)
    (hy : y.val.val=eisensteinTheta • v) :
    Function.Surjective (eisensteinWordResidue v) := by
  have hh := congrArg Subtype.val he
  change eisensteinFramePair (eisensteinClass x.val)=eisensteinFramePair (eisensteinClass y.val) at hh
  rcases (eisensteinFramePair_eq_iff _ _).mp hh with hc|hc
  · exact eisensteinNormalizedFull_class x.val y.val hc hx v hy
  · have hn : eisensteinClass (-x.val)=eisensteinClass y.val := by rw [map_neg,hc,neg_neg]
    exact eisensteinNormalizedFull_class (-x.val) y.val hn (eisensteinNormalizedFull_neg _ hx) v hy

end Atlas.Conway
