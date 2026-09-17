import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section
namespace Atlas.Graphs

/-- Common-neighbor sets transport under the actual graph equivalence. -/
def commonNeighborsEquiv {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W}
    (e : A ≃g B) (x y : V) : A.commonNeighbors x y ≃ B.commonNeighbors (e x) (e y) :=
  e.toEquiv.subtypeEquiv (fun z => by
    change (A.Adj x z ∧ A.Adj y z) ↔ (B.Adj (e x) (e z) ∧ B.Adj (e y) (e z))
    exact and_congr e.map_adj_iff.symm e.map_adj_iff.symm)

/-- For a transitive graph action, neighbor and pair counts at one base vertex
suffice to establish the full strongly regular graph statement. -/
theorem srg_of_transitive_base_counts {G V : Type*} [Group G] [MulAction G V]
    [MulAction.IsPretransitive G V] [Fintype V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (ha : ∀ g : G, ∀ x y : V, A.Adj (g • x) (g • y) ↔ A.Adj x y)
    (v : V) (n k l m : ℕ) (hn : Nat.card V = n)
    (hk : Nat.card (A.neighborSet v) = k)
    (hl : ∀ w, A.Adj v w → Nat.card (A.commonNeighbors v w) = l)
    (hm : ∀ w, v ≠ w → ¬A.Adj v w → Nat.card (A.commonNeighbors v w) = m) :
    A.IsSRGWith n k l m := by
  let e (g : G) : A ≃g A :=
    { toEquiv := MulAction.toPerm g
      map_rel_iff' := ha g _ _ }
  refine ⟨?_,?_,?_,?_⟩
  · exact (Nat.card_eq_fintype_card).symm.trans hn
  · intro x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G v x
    have he := Nat.card_congr ((e g).mapNeighborSet v)
    change Nat.card (A.neighborSet v) = Nat.card (A.neighborSet (g • v)) at he
    rw [hg,hk] at he
    simpa only [Nat.card_eq_fintype_card,A.card_neighborSet_eq_degree] using he.symm
  · intro x y hxy
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G v x
    have hgv : g • (g⁻¹ • y) = y := smul_inv_smul _ _
    have he := Nat.card_congr (commonNeighborsEquiv (e g) v (g⁻¹ • y))
    change Nat.card (A.commonNeighbors v (g⁻¹ • y)) = Nat.card (A.commonNeighbors (g • v) (g • (g⁻¹ • y))) at he
    rw [hg,hgv] at he
    have hh : A.Adj v (g⁻¹ • y) := (ha g _ _).mp (by rwa [hg,hgv])
    rw [hl _ hh] at he
    simpa only [Nat.card_eq_fintype_card] using he.symm
  · intro x y hne hxy
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G v x
    have hgv : g • (g⁻¹ • y) = y := smul_inv_smul _ _
    have he := Nat.card_congr (commonNeighborsEquiv (e g) v (g⁻¹ • y))
    change Nat.card (A.commonNeighbors v (g⁻¹ • y)) = Nat.card (A.commonNeighbors (g • v) (g • (g⁻¹ • y))) at he
    rw [hg,hgv] at he
    have hh : ¬A.Adj v (g⁻¹ • y) := fun h => hxy (by simpa only [hg,hgv] using (ha g _ _).mpr h)
    have hn' : v ≠ g⁻¹ • y := by
      intro h
      exact hne (hg.symm.trans ((congrArg (fun z => g • z) h).trans hgv))
    rw [hm _ hn' hh] at he
    simpa only [Nat.card_eq_fintype_card] using he.symm

end Atlas.Graphs
