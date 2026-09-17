import Atlas.Conway.HSGraphCount
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def hsGraph : SimpleGraph HSGraphPoints where
  Adj y z := integerDot y.val.val z.val.val = 8
  symm := ⟨by intro y z h; rwa [integerDot_comm]⟩
  loopless := ⟨by intro y h; have hy := y.prop.1; omega⟩

def hsWittGraph : SimpleGraph HSWittVertices := hsGraph.comap hsWittGraphMap

def hsWittGraphEquiv : hsWittGraph ≃g hsGraph where
  toEquiv := hsWittVertexEquiv
  map_rel_iff' := Iff.rfl

theorem hs_graph_action_preserves (g : HSModel) (y z : HSGraphPoints) :
    hsGraph.Adj (g • y) (g • z) ↔ hsGraph.Adj y z := by
  change integerDot (g.val.val.val y.val).val (g.val.val.val z.val).val = 8 ↔ _
  rw [g.val.val.prop]
  rfl

theorem hs_base_point_dot (c : HSPointLabels) :
    integerDot (hsWittVector (Sum.inl ())).val
      (hsWittVector (Sum.inr (Sum.inl c))).val = 8 := by
  change integerDot ((normSixVector co3MarkedCoordinate).val-
    (minimumPairPlus co3MarkedCoordinate co3BasePoint.val).val)
    (minimumPairPlus co3MarkedCoordinate c.val.val).val = 8
  have hn : integerDot (normSixVector co3MarkedCoordinate).val
      (minimumPairPlus co3MarkedCoordinate c.val.val).val = 24 :=
    (hs_witt_vector_norms (Sum.inr (Sum.inl c))).2
  rw [integerDot_sub_left,hn,
    co3_point_pair_dot _ _ _ co3BasePoint.prop c.val.prop (by
      intro h; exact c.prop (Subtype.ext h.symm))]
  norm_num

theorem hs_base_hexad_dot (B : HSHexadLabels) :
    integerDot (hsWittVector (Sum.inl ())).val
      (hsWittVector (Sum.inr (Sum.inr B))).val = 16 := by
  change integerDot ((normSixVector co3MarkedCoordinate).val-
    (minimumPairPlus co3MarkedCoordinate co3BasePoint.val).val)
    (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val).val = 16
  have hn : integerDot (normSixVector co3MarkedCoordinate).val
      (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val).val = 24 :=
    (hs_witt_vector_norms (Sum.inr (Sum.inr B))).2
  rw [integerDot_sub_left,hn,
    co3Point_heptad_complement_dot]
  simp [B.prop]

theorem hs_witt_base_point (c : HSPointLabels) :
    hsWittGraph.Adj (Sum.inl ()) (Sum.inr (Sum.inl c)) := hs_base_point_dot c

theorem hs_witt_base_hexad (B : HSHexadLabels) :
    ¬hsWittGraph.Adj (Sum.inl ()) (Sum.inr (Sum.inr B)) := by
  change integerDot (hsWittVector (Sum.inl ())).val
    (hsWittVector (Sum.inr (Sum.inr B))).val ≠ 8
  rw [hs_base_hexad_dot]; decide

theorem hs_witt_points_nonadjacent (c d : HSPointLabels) :
    ¬hsWittGraph.Adj (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d)) := by
  by_cases he : c = d
  · subst d; exact hsWittGraph.loopless.irrefl _
  · change integerDot (minimumPairPlus co3MarkedCoordinate c.val.val).val
      (minimumPairPlus co3MarkedCoordinate d.val.val).val ≠ 8
    rw [co3_point_pair_dot _ _ _ c.val.prop d.val.prop (by
      intro h; exact he (Subtype.ext (Subtype.ext h)))]
    decide

theorem hs_witt_point_hexad (c : HSPointLabels) (B : HSHexadLabels) :
    hsWittGraph.Adj (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inr B)) ↔ c.val ∈ B.val.val := by
  change integerDot (minimumPairPlus co3MarkedCoordinate c.val.val).val
    (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val).val = 8 ↔ _
  rw [co3Point_heptad_complement_dot]
  split_ifs <;> simp_all

theorem hs_hexad_pair_dot (B C : HSHexadLabels) :
    integerDot (hsWittVector (Sum.inr (Sum.inr B))).val
      (hsWittVector (Sum.inr (Sum.inr C))).val = 4*((B.val.val ∩ C.val.val).card+1) := by
  change integerDot ((normSixVector co3MarkedCoordinate).val-(co3HeptadEndpoint _ B.val).val)
    ((normSixVector co3MarkedCoordinate).val-(co3HeptadEndpoint _ C.val).val) = _
  rw [integerDot_sub_left,integerDot_sub_right,integerDot_sub_right,normSixVector_norm,
    co3NormSix_heptad_dot,integerDot_comm (co3HeptadEndpoint _ B.val).val,
    co3NormSix_heptad_dot,co3Heptad_dot]
  ring

theorem hs_witt_hexads_adjacent (B C : HSHexadLabels) :
    hsWittGraph.Adj (Sum.inr (Sum.inr B)) (Sum.inr (Sum.inr C)) ↔
      (B.val.val ∩ C.val.val).card = 1 := by
  change integerDot (hsWittVector (Sum.inr (Sum.inr B))).val
    (hsWittVector (Sum.inr (Sum.inr C))).val = 8 ↔ _
  rw [hs_hexad_pair_dot]
  omega

end Atlas.Conway
