import Atlas.LinearGroups.Chevalley.RootData.ClassicalDPoincareProduct

/-! Geometric-sum arithmetic for the actual type-D Weyl product. Every
subtraction is natural subtraction with q≥1; no factor is cancelled. -/
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData

private theorem even_geometric_product_mul (m q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ m *
      (∏ d ∈ Finset.range m, (∑ k : Fin (2 * (d + 1)), q ^ k.val)) =
        ∏ d ∈ Finset.range m, (q ^ (2 * (d + 1)) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hg : (∑ k : Fin (2 * (m + 1)), q ^ k.val) * (q - 1) =
        q ^ (2 * (m + 1)) - 1 := by
      simpa only [Fin.sum_univ_eq_sum_range] using
        geom_sum_mul_of_one_le hq (2 * (m + 1))
    rw [pow_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    calc
      _ = ((q - 1) ^ m *
          (∏ d ∈ Finset.range m, (∑ k : Fin (2 * (d + 1)), q ^ k.val))) *
            ((∑ k : Fin (2 * (m + 1)), q ^ k.val) * (q - 1)) := by ac_rfl
      _ = _ := by rw [ih, hg]

/-- Multiplying the actual D length sum by its torus factor produces the
fundamental-degree numerator, with degree n+2 retained as an extra factor. -/
theorem rootWeylPoincareEval_D_product_mul (n q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ (n + 2) * rootWeylPoincareEval (pairingD (n + 2)) (baseD n) q =
      (q ^ (n + 2) - 1) *
        ∏ d ∈ Finset.range (n + 1), (q ^ (2 * (d + 1)) - 1) := by
  have hg : (∑ k : Fin (n + 2), q ^ k.val) * (q - 1) = q ^ (n + 2) - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq (n + 2)
  rw [rootWeylPoincareEval_D_product, pow_succ]
  calc
    _ = ((∑ k : Fin (n + 2), q ^ k.val) * (q - 1)) *
        ((q - 1) ^ (n + 1) *
          (∏ d ∈ Finset.range (n + 1), (∑ k : Fin (2 * (d + 1)), q ^ k.val))) := by ac_rfl
    _ = _ := by rw [hg, even_geometric_product_mul (n + 1) q hq]

end Atlas.Chevalley.ClassicalDParabolic
