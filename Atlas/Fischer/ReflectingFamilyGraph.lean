import Atlas.Fischer.ReflectingFamilyMoments
import Atlas.Fischer.ReflectingRootZeroGraph

noncomputable section
namespace Atlas.Fischer
attribute [local instance] Classical.propDecidable

theorem reflectingFamily_nonzero_valency (i : ReflectingRootParameter) :
    (reflectingNonzeroNeighbors reflectingRootParameterVector i).card = 31671 :=
  reflectingNonzeroNeighbors_card _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card i

theorem reflectingFamily_zero_valency (i : ReflectingRootParameter) :
    (reflectingZeroNeighbors reflectingRootParameterVector i).card = 275264 :=
  reflectingZeroNeighbors_card _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card i

theorem reflectingFamily_zero_graph_degree (i : ReflectingRootParameter) :
    (reflectingZeroGraph reflectingRootParameterVector).degree i = 275264 :=
  reflectingZeroGraph_degree _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card i

theorem reflectingFamily_zero_graph_connected :
    (reflectingZeroGraph reflectingRootParameterVector).Connected :=
  reflectingZeroGraph_connected _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card

end Atlas.Fischer
