import Atlas.Conway.Co3TrianglePrimitivity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

instance co3TriangleNontrivial : Nontrivial (Co3Triangles co3MarkedCoordinate) := by
  refine ⟨⟨co3BaseTriangle co3MarkedCoordinate,co3TrianglePair,?_⟩⟩
  intro he
  have ht := congrArg (co3TriangleType co3MarkedCoordinate) he
  rw [co3_base_triangle_type,co3TrianglePair_type] at ht
  exact (by decide : (0 : Fin 8) ≠ 1) ht

theorem co3_mathieu23_maximal : IsCoatom (Co3TriangleStabilizer co3MarkedCoordinate) := by
  rw [← co3_triangle_stabilizer_eq]
  letI := co3_triangles_primitive
  exact IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive Co3MarkedModel (co3BaseTriangle co3MarkedCoordinate)

end Atlas.Conway
