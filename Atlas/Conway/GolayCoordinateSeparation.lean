import Atlas.Lattices.LeechSextetSigns

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem golay_coordinate_separates (i j : Omega) (hij : i ≠ j) :
    ∃ c : golay, c.val i ≠ c.val j := by
  classical
  by_contra h
  push_neg at h
  let w := supportWord {i,j}
  have hw : w ∈ golay := by
    rw [golay_selfDual]
    intro c hc
    have he := h (⟨c,hc⟩ : golay)
    change binaryDot c (supportWord {i,j}) = 0
    rw [tetradSignParity_dot]
    change (∑ k : ({i,j} : Finset Omega), c k) = 0
    rw [Finset.sum_coe_sort]
    rw [Finset.sum_pair hij]
    change c i = c j at he
    rw [he]
    rcases bit_cases (c j) with hh | hh <;> simp [hh]
  have hn : w ≠ 0 := by
    intro he
    have hh := congrFun he i
    simp [w,supportWord] at hh
  have hmin := golay_minimum w hw hn
  have hwt : hammingNorm w = 2 := by
    have he : Finset.univ.filter (fun k => w k ≠ 0) = {i,j} := by
      ext k
      simp [w,supportWord]
      tauto
    change (Finset.univ.filter (fun k => w k ≠ 0)).card = 2
    rw [he,Finset.card_pair hij]
  omega

end Atlas.Conway
