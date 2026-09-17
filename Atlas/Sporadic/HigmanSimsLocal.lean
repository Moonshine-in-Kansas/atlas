import Atlas.Sporadic.HigmanSimsConfiguration
import Atlas.Conway.HSLocalOrbits

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev MathieuModel := HSMathieuModel
abbrev PointStabilizer := HSGraphStabilizer

def mathieu22Embedding : MathieuModel →* Model := hsMathieu22Embedding

def pointStabilizerEquiv : MathieuModel ≃* PointStabilizer := hsMathieuGraphEquiv

theorem mathieu22Embedding_injective : Function.Injective mathieu22Embedding := hsMathieu22Embedding_injective

theorem point_stabilizer_card : Nat.card PointStabilizer = 443520 := hs_graph_stabilizer_card

theorem point_stabilizer_simple : IsSimpleGroup PointStabilizer := hs_graph_stabilizer_simple

theorem faithful : FaithfulSMul Model Points := hs_graph_faithful

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := hs_noncommuting_pair

def localFamily : Points → Fin 3 := hsLocalFamily

def subdegree : Fin 3 → ℕ := hsSubdegree

theorem local_fiber_card (i : Fin 3) : Nat.card {y : Points // localFamily y = i} = subdegree i :=
  hs_local_fiber_card i

theorem local_family_transitive (y z : Points) (h : localFamily y = localFamily z) :
    ∃ g : PointStabilizer, g • y = z := hs_local_family_transitive y z h

theorem point_family_orbit (c : HSPointLabels) :
    MulAction.orbit PointStabilizer (hsPointVector c) = Set.range hsPointVector := hs_stabilizer_point_orbit c

theorem hexad_family_orbit (B : HSHexadLabels) :
    MulAction.orbit PointStabilizer (hsHexadVector B) = Set.range hsHexadVector := hs_stabilizer_hexad_orbit B

end Atlas.Sporadic.HigmanSims
