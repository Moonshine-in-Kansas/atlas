import Atlas.Fischer.ReflectingRootValencies
import Atlas.Graphs.DenseConnected

noncomputable section
namespace Atlas.Fischer
attribute [local instance] Classical.propDecidable

/-- The actual zero-pairing graph, without any group-theoretic interpretation. -/
def reflectingZeroGraph {J : Type*} (r : J → Coordinates) : SimpleGraph J where
  Adj i j := i ≠ j ∧ hermitian (r i) (r j)=0
  symm := by
    constructor
    intro i j h
    refine ⟨Ne.symm h.1,?_⟩
    rw [← hermitian_star,h.2,star_zero]
  loopless := ⟨fun i h => h.1 rfl⟩

theorem reflectingZeroGraph_neighborFinset {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsRoot (r j)) (i : J)
    [Fintype ((reflectingZeroGraph r).neighborSet i)] :
    (reflectingZeroGraph r).neighborFinset i=reflectingZeroNeighbors r i := by
  ext j
  rw [SimpleGraph.mem_neighborFinset]
  simp only [reflectingZeroGraph,
    reflectingZeroNeighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    intro he
    subst j
    rw [(hr i).1] at h
    norm_num at h

/-- Exact regular degree of the actual zero-pairing graph. -/
theorem reflectingZeroGraph_degree {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (i : J) :
    (reflectingZeroGraph r).degree i=275264 := by
  rw [SimpleGraph.degree,reflectingZeroGraph_neighborFinset r (fun j => (hr j).1),
    reflectingZeroNeighbors_card r hr hd hc]

/-- Structural connectedness, derived from the verified degree exceeding half
of the family size; no permutation matrix or group fact is used. -/
theorem reflectingZeroGraph_connected {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) : (reflectingZeroGraph r).Connected := by
  letI : Nonempty J := Fintype.card_pos_iff.mp (by rw [hc]; norm_num)
  apply Atlas.Graphs.connected_of_half_lt_degree
  intro i
  rw [reflectingZeroGraph_degree r hr hd hc,hc]
  norm_num

end Atlas.Fischer
