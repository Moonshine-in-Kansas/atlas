import Atlas.Conway.HSRankThree
import Atlas.GroupTheory.FiniteSuborbitPrimitivity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Only the singleton and whole set pass block divisibility among the local suborbit sums. -/
theorem hs_block_divisibility (T : Finset (Fin 3)) (h0 : 0 ∈ T)
    (hd : (∑ i ∈ T,hsSubdegree i) ∣ 100) :
    (∑ i ∈ T,hsSubdegree i) = 1 ∨ (∑ i ∈ T,hsSubdegree i) = 100 := by
  revert hd h0 T
  decide +kernel

theorem hs_graph_primitive : IsPreprimitive HSModel HSGraphPoints := by
  letI := hs_graph_transitive
  apply Atlas.GroupTheory.primitive_of_suborbit_sums hsBaseGraphPoint hsLocalFamily
    hs_local_family_transitive hsSubdegree hs_local_fiber_card
  intro T ha hd
  have h0 : (0 : Fin 3) ∈ T := by
    change hsLocalFamily (hsWittGraphMap (Sum.inl ())) ∈ T at ha
    rwa [hs_local_family_witt] at ha
  rw [hs_graph_card] at hd ⊢
  exact hs_block_divisibility T h0 hd

end Atlas.Conway
