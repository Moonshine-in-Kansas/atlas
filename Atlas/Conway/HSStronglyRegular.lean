import Atlas.Conway.HSHexadComparison
import Atlas.Graphs.HexadExtensionRegular

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics Atlas.Graphs
attribute [local instance] Classical.propDecidable
local instance : Fintype HSPointLabels := Fintype.ofFinite _
instance hsGraphPointsFintype : Fintype HSGraphPoints := Fintype.ofFinite _

def hsWittHexadVertexEquiv : HSWittVertices ≃
    HexadExtensionVertices (mathieu22Blocks co3MarkedCoordinate co3BasePoint) :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr (Equiv.refl HSPointLabels) hsHexadLabelEquiv)

set_option maxHeartbeats 1000000 in
-- Comparing the nested derived-design subtypes requires additional elaboration.
def hsWittHexadGraphEquiv : hsWittGraph ≃g
    hexadExtensionGraph (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data where
  toEquiv := hsWittHexadVertexEquiv
  map_rel_iff' := by
    intro x y
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (hsWittGraph.loopless.irrefl _)
    · exact iff_of_true trivial (hs_witt_base_point y)
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (hs_witt_base_hexad y)
    · exact iff_of_true trivial (hs_witt_base_point x).symm
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (hs_witt_points_nonadjacent x y)
    · exact (hs_hexad_mem y x).trans (hs_witt_point_hexad x y).symm
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (fun ha => hs_witt_base_hexad x ha.symm)
    · exact (hs_hexad_mem x y).trans ((hs_witt_point_hexad y x).symm.trans (hsWittGraph.adj_comm _ _))
    · simp only [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv,
        Equiv.sumCongr_apply,Sum.map_inr]
      rw [hs_hexads_disjoint_adjacent]
      simp only [Finset.card_eq_zero,Finset.disjoint_iff_inter_eq_empty]
      apply Iff.of_eq
      congr 1
      ext j
      simp only [Finset.mem_inter]

def hsHexadGraphEquiv : hsGraph ≃g
    hexadExtensionGraph (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data :=
  hsWittGraphEquiv.symm.trans hsWittHexadGraphEquiv

theorem hs_graph_strongly_regular : hsGraph.IsSRGWith 100 22 0 6 := by
  have h := hexad_extension_strongly_regular
    (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data hs_point_labels_card
  refine ⟨?_,?_,?_,?_⟩
  · rw [← Nat.card_eq_fintype_card,hs_graph_card]
  · intro x
    rw [← hsHexadGraphEquiv.degree_eq x]
    exact h.regular _
  · intro x y hxy
    have he := Nat.card_congr (commonNeighborsEquiv hsHexadGraphEquiv x y)
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at he
    exact he.trans (h.of_adj _ _ (hsHexadGraphEquiv.map_rel_iff.mpr hxy))
  · intro x y hne hxy
    have he := Nat.card_congr (commonNeighborsEquiv hsHexadGraphEquiv x y)
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at he
    exact he.trans (h.of_not_adj (fun he => hne (hsHexadGraphEquiv.injective he))
      (fun ha => hxy (hsHexadGraphEquiv.map_rel_iff.mp ha)))

end Atlas.Conway
