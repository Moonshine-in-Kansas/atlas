import Atlas.Rudvalis.BinaryBlockWeights

/-! The seven-point balance masks controlling nonzero quadratic cosets. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def balancedBlocks (c b : E) : Finset Point :=
  Finset.univ.filter (fun p => (if p.val=c then (1 : Bit) else 0) + dot b p.val = 1)

/-- There are only eight possible linear adjustments to each nonzero quadratic class. -/
theorem balancedBlocks_sizes (c b : E) (hc : c ≠ 0) :
    (balancedBlocks c b).card = 1 ∨ (balancedBlocks c b).card = 3 ∨
      (balancedBlocks c b).card = 5 := by
  decide +kernel +revert

theorem balancedBlocks_distribution (c : E) (hc : c ≠ 0) :
    (Finset.univ.filter (fun b : E => (balancedBlocks c b).card = 1)).card = 1 ∧
    (Finset.univ.filter (fun b : E => (balancedBlocks c b).card = 3)).card = 4 ∧
    (Finset.univ.filter (fun b : E => (balancedBlocks c b).card = 5)).card = 3 := by
  decide +kernel +revert

theorem blockWeight_quadratic_lower (a : Bit) (b c : E) (hc : c ≠ 0) :
    2 ≤ blockWeight a b c := by
  have h := blockWeight_quadratic a b c hc
  split_ifs at h <;> omega

/-- The whole nonzero quadratic coset has minimum at least sixteen. -/
theorem binaryNormalMap_quadratic_lower (a : BinaryParameters) (hc : a.2.2 ≠ 0) :
    16 ≤ hammingNorm (binaryNormalMap a) := by
  classical
  have hs := balancedBlocks_sizes a.2.2 (matrixAt a.2.1.transpose a.2.2) hc
  have hp : (balancedBlocks a.2.2 (matrixAt a.2.1.transpose a.2.2)).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨p,hp⟩ := hp
  have hp' : quadratic a.2.2 a.2.2 +
      dot (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 = 1 := by
    rw [binary_balance_mask]
    exact (Finset.mem_filter.mp hp).2
  have hw := blockWeight_quadratic (a.1 p) (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 hc
  simp only [hp', if_true] at hw
  have hsum0 : ∀ p : Point, (∑ q : Point, if q=p then (4 : ℕ) else 2) = 16 := by
    decide +kernel
  have hsum := hsum0 p
  rw [binaryNormalMap_weight, ← hsum]
  apply Finset.sum_le_sum
  intro q _
  split_ifs with hq
  · subst q
    omega
  · exact blockWeight_quadratic_lower _ _ _ hc

end Atlas.Rudvalis
