import Atlas.Fischer.MarkedParkerResidueTransport
import Atlas.Fischer.OctadicResidueFusion
import Atlas.Fischer.ResidueKernelDuads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every original noncommuting residue point is carried to an eligible
actual duadic point by an element fixing S and the base coordinate. -/
theorem residue_noncommuting_to_duadic (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (y : ResiduePoint S)
    (hy : ¬ Commute (distinguishedRootElement (.inl x)) y.val) :
    ∃ p : RootDuad,S ⊆ p.val ∧ x∉p.val ∧
      ∃ ξ : Module.Dual Bit (duadShortenedCode p.val),
        ∃ g : residueCentralizer (insert x S),
          (MulAut.conj g.val) y.val=distinguishedRootElement (.inr (.inr ⟨p,ξ⟩)) := by
  obtain ⟨t,ht⟩ := y.prop.1
  have hc (i : Omega) (hi : i∈S) := y.prop.2.2 i hi
  rw [← ht] at hy hc ⊢
  rcases t with i | (⟨O,χ⟩ | ⟨p,ξ⟩)
  · exact (hy (standardCommutingFrame_isFrame.2.1 _ ⟨x,rfl⟩ _ ⟨i,rfl⟩)).elim
  · have hSO : S ⊆ O.val := by
      intro i hi
      have hn := distinguishedRoot_commute_nonzero _ _ (hc i hi)
      change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration O) χ)≠0 at hn
      by_contra h
      rw [hermitian_basicAxis_octadic,if_neg h] at hn
      exact hn rfl
    have hxO : x∉O.val := by
      intro hx
      apply hy
      apply (distinguishedRoot_commute_iff _ _).mpr
      change hermitian (basicAxis x) (octadicRoot (chosenOctadCalibration O) χ)≠0
      rw [hermitian_basicAxis_octadic,if_pos hx]
      exact one_ne_zero
    exact octadic_residue_fusion S hS x O hSO hxO χ
  · have hSp : S ⊆ p.val := by
      intro i hi
      have hn := distinguishedRoot_commute_nonzero _ _ (hc i hi)
      change hermitian (basicAxis i) (chosenDuadicRoot p ξ)≠0 at hn
      by_contra h
      rw [hermitian_basicAxis_duadic,if_neg h] at hn
      exact hn rfl
    have hxp : x∉p.val := by
      intro hx
      apply hy
      apply (distinguishedRoot_commute_iff _ _).mpr
      change hermitian (basicAxis x) (chosenDuadicRoot p ξ)≠0
      rw [hermitian_basicAxis_duadic,if_pos hx]
      exact one_ne_zero
    exact ⟨p,hSp,hxp,ξ,1,by simp⟩

/-- The full noncommuting suborbit on original residue points, with the actual
centralizer of the enlarged marking as transporter. -/
theorem residue_noncommuting_transitive (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (y z : ResiduePoint S)
    (hy : ¬ Commute (distinguishedRootElement (.inl x)) y.val)
    (hz : ¬ Commute (distinguishedRootElement (.inl x)) z.val) :
    ∃ g : residueCentralizer (insert x S),(MulAut.conj g.val) y.val=z.val := by
  obtain ⟨p,hSp,hxp,ξ,a,ha⟩ := residue_noncommuting_to_duadic S hS x y hy
  obtain ⟨q,hSq,hxq,η,b,hb⟩ := residue_noncommuting_to_duadic S hS x z hz
  obtain ⟨c,hc⟩ := residue_marked_duadic_transitive S hS x p q hSp hSq hxp hxq ξ η
  change a.val*y.val*a.val⁻¹=distinguishedRootElement (.inr (.inr ⟨p,ξ⟩)) at ha
  change b.val*z.val*b.val⁻¹=distinguishedRootElement (.inr (.inr ⟨q,η⟩)) at hb
  change c.val*distinguishedRootElement (.inr (.inr ⟨p,ξ⟩))*c.val⁻¹=
    distinguishedRootElement (.inr (.inr ⟨q,η⟩)) at hc
  refine ⟨b⁻¹*c*a,?_⟩
  change (b.val⁻¹*c.val*a.val)*y.val*(b.val⁻¹*c.val*a.val)⁻¹=z.val
  calc
    _ = b.val⁻¹*(c.val*(a.val*y.val*a.val⁻¹)*c.val⁻¹)*b.val := by group
    _ = b.val⁻¹*(b.val*z.val*b.val⁻¹)*b.val := by rw [ha,hc,← hb]
    _ = z.val := by group

end Atlas.Fischer
