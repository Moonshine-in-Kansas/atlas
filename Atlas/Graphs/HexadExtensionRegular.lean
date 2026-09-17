import Atlas.Graphs.HexadExtensionGraph
import Atlas.Graphs.TransitiveStronglyRegular

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Graphs
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem hexad_extension_common_card (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (x y : HexadExtensionVertices blocks) (hxy : x ≠ y) :
    Nat.card {z // (hexadExtensionGraph blocks h).Adj x z ∧
      (hexadExtensionGraph blocks h).Adj y z} =
      if (hexadExtensionGraph blocks h).Adj x y then 0 else 6 := by
  have hs (x y : HexadExtensionVertices blocks) :
      Nat.card {z // (hexadExtensionGraph blocks h).Adj x z ∧
        (hexadExtensionGraph blocks h).Adj y z} =
      Nat.card {z // (hexadExtensionGraph blocks h).Adj y z ∧
        (hexadExtensionGraph blocks h).Adj x z} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  · exact False.elim (hxy rfl)
  · exact hexad_extension_base_common blocks h _ (by simp)
  · exact hexad_extension_base_common blocks h _ (by simp)
  · rw [hs]
    exact hexad_extension_base_common blocks h _ (by simp)
  · simpa only [hexadExtensionGraph,hexadExtensionAdj,ite_false] using hexad_extension_points_common blocks h x y (fun he => hxy (congrArg (fun t => Sum.inr (Sum.inl t)) he))
  · convert hexad_extension_point_block_common blocks h x y using 1
    split_ifs <;> simp_all only [hexadExtensionGraph,hexadExtensionAdj,not_true_eq_false]
  · rw [hs]
    exact hexad_extension_base_common blocks h _ (by simp)
  · rw [hs]
    convert hexad_extension_point_block_common blocks h y x using 1
    split_ifs <;> simp_all only [hexadExtensionGraph,hexadExtensionAdj,not_true_eq_false]
  · convert hexad_extension_blocks_common blocks h x y (fun he => hxy (congrArg (fun t => Sum.inr (Sum.inr t)) he)) using 1
    split_ifs <;> simp_all only [hexadExtensionGraph,hexadExtensionAdj,not_true_eq_false]

theorem hexad_extension_strongly_regular (blocks : Finset (Finset V))
    (h : HexadDesignData blocks) (hv : Nat.card V = 22) :
    (hexadExtensionGraph blocks h).IsSRGWith 100 22 0 6 where
  card := by
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_unit,Fintype.card_coe,
      ← Nat.card_eq_fintype_card,hv,h.card]
  regular := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    exact hexad_extension_neighbor_card blocks h hv x
  of_adj := by
    intro x y hxy
    rw [← Nat.card_eq_fintype_card]
    exact (hexad_extension_common_card blocks h x y hxy.ne).trans (if_pos hxy)
  of_not_adj := by
    intro x y hne hxy
    rw [← Nat.card_eq_fintype_card]
    exact (hexad_extension_common_card blocks h x y hne).trans (if_neg hxy)

end Atlas.Graphs
