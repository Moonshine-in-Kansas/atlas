import Atlas.Conway.HSConfiguration

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway
attribute [local instance] Classical.propDecidable

/-- The full pointwise stabilizer of the marked Leech triangle. -/
abbrev Model := HSModel
abbrev Sides := HSSides
abbrev Points := HSGraphPoints
abbrev WittVertices := HSWittVertices

def endpoint := hsEndpoint
def baseSide : Sides := hsBaseSide
def basePoint : Points := hsWittGraphMap (Sum.inl ())
def graph := hsGraph
def wittGraph := hsWittGraph
def wittGraphEquiv : wittGraph ≃g graph := hsWittGraphEquiv
def hexadGraphEquiv := hsHexadGraphEquiv

theorem sides_card : Nat.card Sides = 11178 := hs_sides_card

def sideParameterEquiv := hsSideParameterEquiv

def wittVertexEquiv : WittVertices ≃ Points := hsWittVertexEquiv

theorem degree : Nat.card Points = 100 := hs_graph_card

theorem strongly_regular : graph.IsSRGWith 100 22 0 6 := hs_graph_strongly_regular

theorem connected : graph.Connected := hs_graph_connected

theorem adjacent_iff_distance (u v : Points) : graph.Adj u v ↔
    integerDot (u.val-v.val).val (u.val-v.val).val = 48 := hs_graph_adjacency_distance u v

theorem nonadjacent_inner_product (u v : Points) (hne : u ≠ v) (ha : ¬graph.Adj u v) :
    integerDot u.val.val v.val.val = 16 := hs_graph_nonadjacent_dot u v hne ha

theorem graph_action_preserves (g : Model) (u v : Points) :
    graph.Adj (g • u) (g • v) ↔ graph.Adj u v := hs_graph_action_preserves g u v

end Atlas.Sporadic.HigmanSims
