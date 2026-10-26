import Atlas.Rudvalis.RankOneMatrices

/-! Four active Fano evaluations characterize the nonzero rank-one matrices. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def linearOnes (b : E) : Finset Point := Finset.univ.filter (fun p => dot b p.val = 1)

theorem linearOnes_injective : Function.Injective linearOnes := by
  intro b d h
  have hp (p : Point) : dot b p.val = 1 ↔ dot d p.val = 1 := by
    have he := Finset.ext_iff.mp h p
    simpa [linearOnes] using he
  ext i
  have hi := hp (basisPoint i)
  have he : b i = 1 ↔ d i = 1 := by
    fin_cases i <;> simpa [basisPoint,binaryLabel,dot,Fin.sum_univ_succ] using hi
  rcases Atlas.Codes.bit_cases (b i) with hb | hb <;>
    rcases Atlas.Codes.bit_cases (d i) with hd | hd <;> simp_all

theorem linearOnes_row_subset (M : BinaryMatrix) (j : Fin 3) :
    linearOnes (M j) ⊆ nonzeroMatrixBlocks M := by
  intro p hp
  simp only [linearOnes,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  simp only [nonzeroMatrixBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  intro hz
  have he := congrFun hz j
  change dot (M j) p.val = 0 at he
  rw [hp] at he
  exact one_ne_zero he

theorem fourActive_isBinaryRankOne (M : BinaryMatrix) (hM : M ≠ 0)
    (hcard : (nonzeroMatrixBlocks M).card = 4) : isBinaryRankOne M := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, M i ≠ 0 := Function.ne_iff.mp hM
  have he (j : Fin 3) (hj : M j ≠ 0) : linearOnes (M j) = nonzeroMatrixBlocks M := by
    apply Finset.eq_of_subset_of_card_le (linearOnes_row_subset M j)
    rw [hcard]
    exact (linear_ones_count (M j) hj).ge
  have hr (j : Fin 3) (hj : M j ≠ 0) : M j = M i :=
    linearOnes_injective ((he j hj).trans (he i hi).symm)
  let b : E := fun j => if M j = 0 then 0 else 1
  have hb : b ≠ 0 := by
    intro hb
    have he := congrFun hb i
    simp [b,hi] at he
  refine ⟨⟨b,hb⟩,⟨M i,hi⟩, ?_⟩
  ext j k
  by_cases hj : M j = 0
  · simp [outerMatrix,b,hj]
  · simp [outerMatrix,b,hj,hr j hj,hi]

theorem outerMatrix_active (b u : Point) :
    nonzeroMatrixBlocks (outerMatrix b.val u.val) = linearOnes u.val := by
  ext p
  simp only [nonzeroMatrixBlocks,linearOnes,Finset.mem_filter,Finset.mem_univ,true_and,
    matrixAt_outer]
  rcases Atlas.Codes.bit_cases (dot u.val p.val) with h | h <;> simp [h,b.prop]

theorem isBinaryRankOne_iff (M : BinaryMatrix) :
    isBinaryRankOne M ↔ M ≠ 0 ∧ (nonzeroMatrixBlocks M).card = 4 := by
  constructor
  · rintro ⟨b,u,rfl⟩
    refine ⟨outerMatrix_nonzero _ _ b.prop u.prop, ?_⟩
    rw [outerMatrix_active]
    exact linear_ones_count _ u.prop
  · rintro ⟨hM,hc⟩
    exact fourActive_isBinaryRankOne M hM hc

end Atlas.Rudvalis
