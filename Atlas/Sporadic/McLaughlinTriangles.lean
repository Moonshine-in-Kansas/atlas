import Atlas.Sporadic.McLaughlinGraph
import Atlas.Conway.McLTriangleFaithful

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev Triangles := McLTriangles

def baseTriangle : Triangles := mclBaseTriangle

abbrev TriangleStabilizer := McLTriangleStabilizer

def triangleMathieuEquiv : McLMathieuModel ≃* TriangleStabilizer := mclMathieuTriangleEquiv

def triangleParameterEquiv := mclTriangleParameterEquiv

def triangleType : Triangles → Fin 4 := mclTriangleType

theorem triangle_degree : Nat.card Triangles = 2025 := mcl_triangles_card

theorem triangle_subdegree (t : Fin 4) :
    Nat.card {y : Triangles // triangleType y = t} = mclTriangleSize t := mcl_triangle_type_card t

theorem triangle_mathieu_orbits (x y : Triangles) :
    (∃ g : McLMathieuModel, mathieu22Embedding g • x = y) ↔
      triangleType x = triangleType y := mcl_triangle_mathieu_orbit_iff x y

theorem triangles_transitive : MulAction.IsPretransitive Model Triangles := mcl_triangles_transitive

theorem triangles_primitive : MulAction.IsPreprimitive Model Triangles := mcl_triangles_primitive

theorem triangles_faithful : FaithfulSMul Model Triangles := mcl_triangles_faithful

theorem triangle_stabilizer_card : Nat.card TriangleStabilizer = 443520 := mcl_triangle_stabilizer_card

theorem triangle_stabilizer_simple : IsSimpleGroup TriangleStabilizer := mcl_triangle_stabilizer_simple

theorem triangle_stabilizer_maximal : IsCoatom TriangleStabilizer := by
  letI : Nontrivial Triangles := Finite.one_lt_card_iff_nontrivial.mp (by rw [triangle_degree]; decide)
  letI := triangles_primitive
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive Model baseTriangle

end Atlas.Sporadic.McLaughlin
