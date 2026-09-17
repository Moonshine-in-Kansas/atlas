import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace Atlas.Graphs

/-- Two sufficiently large neighbor sets intersect; this is a finite-set argument. -/
theorem common_neighbor_of_card_lt_degree_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (h : Fintype.card V < G.degree x+G.degree y) :
    ∃ z, G.Adj x z ∧ G.Adj y z := by
  classical
  have hc := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  have hu : (G.neighborFinset x ∪ G.neighborFinset y).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have hi : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree] at h
    omega
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hi
  refine ⟨z,?_⟩
  simpa only [Finset.mem_inter,SimpleGraph.mem_neighborFinset] using hz

/-- A finite nonempty graph of minimum degree greater than half its vertex count
is connected: every two vertices have a common neighbor. -/
theorem connected_of_half_lt_degree {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ x, Fintype.card V < 2*G.degree x) : G.Connected := by
  constructor
  intro x y
  obtain ⟨z,hx,hy⟩ := common_neighbor_of_card_lt_degree_sum G x y (by
    have h1 := h x
    have h2 := h y
    omega)
  exact hx.reachable.trans hy.symm.reachable

end Atlas.Graphs
