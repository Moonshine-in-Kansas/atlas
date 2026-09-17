import Atlas.Conway.Co3Decompositions

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimum_decomposition_member (x : leech) (p : MinimumDecompositions x)
    (v : leech) (hv : v ∈ p.val) : integerDot v.val v.val = 32 ∧
    integerDot (x-v).val (x-v).val = 32 ∧ p.val = {v,x-v} := by
  obtain ⟨y,hy,hz,hp⟩ := p.prop
  rw [hp,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨hy,hz,hp⟩
  · rw [sub_sub_cancel,Finset.pair_comm]
    exact ⟨hz,hy,hp⟩

end Atlas.Conway
