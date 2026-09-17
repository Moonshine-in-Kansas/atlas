import Atlas.Sporadic.Conway3
import Atlas.Conway.Co3DecompositionFaithful
import Atlas.Conway.Co3MathieuOrbits

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev Points := MinimumDecompositions vector.val
abbrev PointHeptad := Co3PointHeptad ((0,0),0)

def pointHeptadEquiv : PointHeptad ≃ Points := co3PointHeptadDecompositionEquiv _

theorem degree : Nat.card Points = 276 := co3_decompositions_card _

theorem faithful : FaithfulSMul Model Points := co3_decompositions_faithful

theorem pointHeptad_equivariant (g : Mathieu23PointModel ((0,0),0)) (p : PointHeptad) :
    pointHeptadEquiv (co3PointHeptadMap _ g p) = mathieu23Embedding g • pointHeptadEquiv p :=
  co3PointHeptadDecomposition_equivariant _ g p

def triangleVector : leech := oddMinimumVector ((0,0),0) 0

abbrev TriangleStabilizer := MulAction.stabilizer Model triangleVector

def triangleMathieuEquiv : Mathieu23PointModel ((0,0),0) ≃* TriangleStabilizer :=
  mathieu23TriangleEquiv _

theorem triangle_stabilizer_card : Nat.card TriangleStabilizer = 10200960 := by
  rw [← Nat.card_congr triangleMathieuEquiv.toEquiv,mathieu23_order]

theorem triangle_norms : integerDot triangleVector.val triangleVector.val = 32 ∧
    integerDot (vector.val-triangleVector).val (vector.val-triangleVector).val = 64 :=
  co3_base_triangle_norms _

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := by
  obtain ⟨g,h,hne⟩ := mathieu23_noncommuting_pair ((0,0),0)
  refine ⟨mathieu23Embedding g,mathieu23Embedding h,?_⟩
  intro he
  apply hne
  apply mathieu23Embedding_injective
  simpa only [map_mul] using he

end Atlas.Sporadic.Conway3
