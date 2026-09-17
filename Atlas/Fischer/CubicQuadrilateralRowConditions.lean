import Atlas.Fischer.CubicQuadrilateralFunctions
import Atlas.Fischer.CubicQuadrilateralIndicatorCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def CubicQuadrilateralRow (D F G : Octad) : Fin 8 → Prop := ![
  (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 4 ∧
    (F.val ∩ G.val).card = 4 ∧ (D.val ∩ F.val ∩ G.val).card = 0,
  (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 4 ∧
    (F.val ∩ G.val).card = 4 ∧ (D.val ∩ F.val ∩ G.val).card = 2,
  (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 4 ∧
    (F.val ∩ G.val).card = 4 ∧ (D.val ∩ F.val ∩ G.val).card = 3,
  (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 4 ∧
    (F.val ∩ G.val).card = 4 ∧ (D.val ∩ F.val ∩ G.val).card = 4,
  (D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 4 ∧ (F.val ∩ G.val).card = 0,
  (((D.val ∩ F.val).card = 0 ∧ (D.val ∩ G.val).card = 4) ∨
    ((D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 0)) ∧
    ((F.val ∩ G.val).card = 4 ∨ (F.val ∩ G.val).card = 0),
  (D.val ∩ F.val).card = 0 ∧ (D.val ∩ G.val).card = 0 ∧ (F.val ∩ G.val).card = 4,
  (D.val ∩ F.val).card = 0 ∧ (D.val ∩ G.val).card = 0 ∧ (F.val ∩ G.val).card = 0]

def cubicQuadrilateralRowWeight : Fin 8 → Scalar := ![1,1,-1,1,-3,3,-3,9]
def cubicQuadrilateralRowIntersection : Fin 8 → ℕ := ![8,4,2,0,0,4,0,8]
def cubicQuadrilateralRowCard : Fin 8 → ℕ := ![280,280*72,280*64,280*3,840,3360,840,30]

theorem cubicQuadrilateralRow_admissible (D F G : Octad) (n : Fin 8)
    (h : CubicQuadrilateralRow D F G n) :
    OctadPairAdmissible D F ∧ OctadPairAdmissible D G ∧ OctadPairAdmissible F G := by
  fin_cases n <;> dsimp [CubicQuadrilateralRow] at h <;>
    unfold OctadPairAdmissible <;> omega

theorem cubicQuadrilateralRow_exhaustive (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G) : ∃ n, CubicQuadrilateralRow D F G n := by
  rcases hDF with hf | hf <;> rcases hDG with hg | hg <;> rcases hFG with hk | hk
  · rcases cubicCommonNeighbor_actual_levels D F G hf hg hk with hu | hu | hu | hu
    · exact ⟨0,hf,hg,hk,hu⟩
    · exact ⟨1,hf,hg,hk,hu⟩
    · exact ⟨2,hf,hg,hk,hu⟩
    · exact ⟨3,hf,hg,hk,hu⟩
  · exact ⟨4,hf,hg,hk⟩
  · exact ⟨5,Or.inr ⟨hf,hg⟩,Or.inl hk⟩
  · exact ⟨5,Or.inr ⟨hf,hg⟩,Or.inr hk⟩
  · exact ⟨5,Or.inl ⟨hf,hg⟩,Or.inl hk⟩
  · exact ⟨5,Or.inl ⟨hf,hg⟩,Or.inr hk⟩
  · exact ⟨6,hf,hg,hk⟩
  · exact ⟨7,hf,hg,hk⟩

theorem cubicQuadrilateralRow_unique (D F G : Octad) (n m : Fin 8)
    (hn : CubicQuadrilateralRow D F G n) (hm : CubicQuadrilateralRow D F G m) : n = m := by
  fin_cases n <;> fin_cases m <;>
    dsimp [CubicQuadrilateralRow] at hn hm ⊢ <;> first | rfl | omega

end Atlas.Fischer
