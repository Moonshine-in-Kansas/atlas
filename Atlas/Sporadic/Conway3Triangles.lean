import Atlas.Sporadic.Conway3Geometry
import Atlas.Conway.Co3TriangleCount

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

/-- Intrinsic oriented 2-3-4 Leech triangles with fixed norm-six side. -/
abbrev Triangles := Co3Triangles ((0,0),0)

instance triangleAction : MulAction Model Triangles := co3TrianglesAction ((0,0),0)

def baseTriangle : Triangles := co3BaseTriangle _

theorem triangles_card : Nat.card Triangles = 48600 := co3_triangles_card _

def triangleParametersEquiv :
    ((t : Fin 8) × Co3TriangleParameters ((0,0),0) t) ≃ Triangles := co3TriangleEquiv _

theorem triangle_shape_card (t : Fin 8) :
    Nat.card {y : leech // Co3TriangleShape ((0,0),0) t y} = co3TriangleSize t :=
  co3_triangle_shape_card _ t

theorem triangle_stabilizer_eq : MulAction.stabilizer Model baseTriangle = TriangleStabilizer :=
  co3_triangle_stabilizer_eq _

end Atlas.Sporadic.Conway3
