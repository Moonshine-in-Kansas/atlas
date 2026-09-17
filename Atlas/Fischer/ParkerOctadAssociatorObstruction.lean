import Atlas.Fischer.ParkerOctadUniformSign
import Atlas.Fischer.CubicCommonNeighborDistribution
import Atlas.Fischer.CubicCompletionIntersections
import Atlas.Fischer.ParkerInterchange
import Atlas.Fischer.ParkerCenter

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Odd actual triple incidence has odd Parker associator sign. -/
theorem parkerOctadTriple_three (D F G : Octad)
    (htr : ((D.val ∩ F.val) ∩ G.val).card = 3) :
    parkerTripleIntersection (octadWord D) (octadWord F) (octadWord G) = 1 := by
  rw [← parkerTripleCount_cast]
  have hcount := cubicOctadTripleCount G D F
  have hset : ((G.val ∩ D.val) ∩ F.val) = ((D.val ∩ F.val) ∩ G.val) := by
    rw [Finset.inter_assoc, Finset.inter_comm G.val (D.val ∩ F.val)]
  rw [hset,htr] at hcount
  rw [hcount]
  decide

/-- The actual odd triple-intersection
 configuration prevents any choice of
octad lifts from having a uniform product sign on octadic sums. -/
theorem parkerOctad_uniform_sign_impossible
    (q : Octad → ParkerLoop) (hq : ∀ O, (q O).1 = octadWord O)
    (e : Bit)
    (he : ∀ D E F : Octad, octadWord F = octadWord D + octadWord E →
      parkerLoopMultiply (q D) (q E) = parkerSign e (q F)) : False := by
  classical
  let D := countingCanonicalD
  let F := countingCanonicalSextetE
  have hDF : (D.val ∩ F.val).card = 4 := by
    simpa only [signedOctadIntersection,signedOctadSupport_canonical] using
      octadWord_sum_weight countingCanonicalSextetF D F countingCanonicalSextet_word
  have hc := (cubicCommonNeighbor_distribution D F hDF).2.2.1
  have hn : Nonempty (CubicCommonNeighbors D F 3) :=
    Finite.card_pos_iff.mp (by change 0 < cubicCommonNeighborCount D F 3; rw [hc]; decide)
  obtain ⟨⟨G,hDG,hFG,htr⟩⟩ := hn
  let A := cubicSextetCompletion D F hDF
  let U := cubicSextetCompletion F G hFG
  let V := cubicSextetCompletion D G hDG
  have hA : octadWord A = octadWord D + octadWord F := cubicSextetCompletion_word _ _ _
  have hU : octadWord U = octadWord F + octadWord G := cubicSextetCompletion_word _ _ _
  have hV : octadWord V = octadWord D + octadWord G := cubicSextetCompletion_word _ _ _
  have hAF : octadWord D = octadWord A + octadWord F := by
    rw [hA,add_assoc,parkerGolay_add_self,add_zero]
  have hAU : octadWord V = octadWord A + octadWord U := by
    rw [hA,hU,hV]
    calc
      _ = octadWord D + (octadWord F + octadWord F) + octadWord G := by
        rw [parkerGolay_add_self,add_zero]
      _ = _ := by abel
  have hl : parkerLoopMultiply (parkerLoopMultiply (q A) (q F)) (q G) = q V := by
    rw [he A F D hAF, parkerLoopMultiply_sign_left, he D G V hV,
      parkerSign_add, CharTwo.add_self_eq_zero, parkerSign_zero]
  have hr : parkerLoopMultiply (q A) (parkerLoopMultiply (q F) (q G)) = q V := by
    rw [he F G U hU, parkerLoopMultiply_sign_right, he A U V hAU,
      parkerSign_add, CharTwo.add_self_eq_zero, parkerSign_zero]
  have ht : parkerTripleIntersection (q A).1 (q F).1 (q G).1 = 1 := by
    rw [hq,hq,hq,hA]
    simp only [Submodule.coe_add,parkerTripleIntersection_add_first]
    have hz : parkerTripleIntersection (octadWord F) (octadWord F) (octadWord G) = 0 := by
      rw [parkerTripleIntersection_cycle, parkerTripleIntersection_swap,
        parkerTripleIntersection_repeat]
    rw [hz,add_zero]
    exact parkerOctadTriple_three D F G htr

  have ha := parkerLoopMultiply_associator (q A) (q F) (q G)
  rw [hl,hr,ht] at ha
  have hz := (parkerSign_eq_self_iff 1 (q V)).mp ha.symm
  exact one_ne_zero hz

end Atlas.Fischer
