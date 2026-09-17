import Atlas.Sporadic.Conway3Triangles
import Atlas.Conway.Co3MathieuMaximal

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

def triangleType : Triangles → Fin 8 := co3TriangleType co3MarkedCoordinate

theorem triangle_subdegree (t : Fin 8) :
    Nat.card {y : Triangles // triangleType y = t} = co3TriangleSize t := co3_triangle_type_card _ t

theorem triangle_mathieu_orbits (x y : Triangles) :
    (∃ g : Mathieu23PointModel co3MarkedCoordinate, mathieu23Embedding g • x = y) ↔
      triangleType x = triangleType y := co3_triangle_mathieu_orbit_iff _ x y

theorem triangles_transitive : MulAction.IsPretransitive Model Triangles := co3_triangles_transitive

theorem triangles_primitive : MulAction.IsPreprimitive Model Triangles := co3_triangles_primitive

theorem triangle_stabilizer_maximal : IsCoatom TriangleStabilizer := co3_mathieu23_maximal

end Atlas.Sporadic.Conway3
