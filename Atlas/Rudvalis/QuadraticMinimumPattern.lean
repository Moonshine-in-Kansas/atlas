import Atlas.Rudvalis.ConstantRows

/-! The equality case in the quadratic residue lower bound. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem balancedBlocks_unique (c b : E) (hc : c ≠ 0) (p : Point)
    (h : ∀ q : Point, q ∈ balancedBlocks c b ↔ q = p) : b = 0 ∧ p.val = c := by
  simp only [balancedBlocks,Finset.mem_filter,Finset.mem_univ,true_and] at h
  decide +kernel +revert

theorem blockWeight_four_iff (a : Bit) (b c : E) (hc : c ≠ 0) :
    blockWeight a b c = 4 ↔ quadratic c c + dot b c = 1 := by
  have h := blockWeight_quadratic a b c hc
  split_ifs at h with hh
  · simp only [hh,iff_true]; exact h
  · simp only [hh,iff_false]; omega

theorem binaryNormalMap_quadratic_weight_sixteen (a : BinaryParameters) (hc : a.2.2 ≠ 0) :
    hammingNorm (binaryNormalMap a) = 16 ↔
      ∀ p : Point, blockWeight (a.1 p) (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 =
        if p.val = a.2.2 then 4 else 2 := by
  classical
  have hs (p : Point) : (∑ q : Point, if q=p then (4 : ℕ) else 2) = 16 := by
    decide +kernel +revert
  constructor
  · intro hw
    have hsize := balancedBlocks_sizes a.2.2 (matrixAt a.2.1.transpose a.2.2) hc
    obtain ⟨p,hp⟩ : (balancedBlocks a.2.2 (matrixAt a.2.1.transpose a.2.2)).Nonempty := by
      apply Finset.card_pos.mp
      omega
    have hpw : blockWeight (a.1 p) (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 = 4 := by
      apply (blockWeight_four_iff _ _ _ hc).mpr
      rw [binary_balance_mask]
      exact (Finset.mem_filter.mp hp).2
    have hl : ∀ q ∈ (Finset.univ : Finset Point),
        (if q=p then 4 else 2) ≤
          blockWeight (a.1 q) (matrixAt a.2.1 q.val + eta q a.2.2) a.2.2 := by
      intro q _
      split_ifs with hq
      · subst q; omega
      · exact blockWeight_quadratic_lower _ _ _ hc
    have he : ∀ q : Point, (if q=p then 4 else 2) =
        blockWeight (a.1 q) (matrixAt a.2.1 q.val + eta q a.2.2) a.2.2 := by
      intro q
      exact (Finset.sum_eq_sum_iff_of_le hl).mp
        (by rw [hs,← binaryNormalMap_weight,hw]) q (Finset.mem_univ q)
    have hmask : ∀ q : Point,
        q ∈ balancedBlocks a.2.2 (matrixAt a.2.1.transpose a.2.2) ↔ q=p := by
      intro q
      have hq := blockWeight_four_iff (a.1 q)
        (matrixAt a.2.1 q.val + eta q a.2.2) a.2.2 hc
      rw [binary_balance_mask,← he q] at hq
      simp only [balancedBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [← hq]
      split_ifs <;> simp_all
    have hpc := (balancedBlocks_unique _ _ hc p hmask).2
    intro q
    rw [← he q]
    have hqp : q=p ↔ q.val=a.2.2 := by rw [← hpc]; exact Subtype.ext_iff
    simp only [hqp]
  · intro h
    rw [binaryNormalMap_weight]
    have hp : (⟨a.2.2,hc⟩ : Point).val = a.2.2 := rfl
    have hsum := hs (⟨a.2.2,hc⟩ : Point)
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro p _
    rw [h]
    have he : p.val=a.2.2 ↔ p=(⟨a.2.2,hc⟩ : Point) :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [he]

theorem binaryNormalMap_quadratic_minimum_contraction (a : BinaryParameters)
    (hc : a.2.2 ≠ 0) (hw : hammingNorm (binaryNormalMap a) = 16) :
    matrixAt a.2.1.transpose a.2.2 = 0 := by
  have hpattern := (binaryNormalMap_quadratic_weight_sixteen a hc).mp hw
  apply (balancedBlocks_unique a.2.2 (matrixAt a.2.1.transpose a.2.2) hc
    (⟨a.2.2,hc⟩ : Point) ?_).1
  intro p
  have hp := blockWeight_four_iff (a.1 p)
    (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 hc
  rw [hpattern p,binary_balance_mask] at hp
  simp only [balancedBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← hp]
  have he : p.val=a.2.2 ↔ p=(⟨a.2.2,hc⟩ : Point) :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  by_cases hv : p.val = a.2.2
  · simp only [if_pos hv]
    exact ⟨fun _ => he.mp hv, fun _ => True.intro⟩
  · simp only [if_neg hv]
    constructor
    · intro h; omega
    · intro h; exact (hv (he.mpr h)).elim

end Atlas.Rudvalis

