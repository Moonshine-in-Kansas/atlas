import Atlas.LinearAlgebra.QuadraticDiscriminantClassification

/-! # A normalized basis with all but the last quadratic coefficient equal to one -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [Finite F] [Invertible (2 : F)]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem finite_nondegenerate_normal_form (h2 : (2 : F) ≠ 0)
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
    (n : ℕ) (hd : Module.finrank F V = n + 1) :
    ∃ d : F, d ≠ 0 ∧ Nonempty (Q.IsometryEquiv (diagonalForm (normalWeights n d))) := by
  have hh := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (associated_separating_of_polar_nondegenerate Q hQ)
  rw [hd] at hh
  obtain ⟨w,⟨e⟩⟩ := hh
  obtain ⟨f⟩ := finite_unit_diagonal_normalization h2 n w
  exact ⟨∏ i, (w i : F),Finset.prod_ne_zero_iff.mpr (fun i _ => (w i).ne_zero),⟨e.trans f⟩⟩

omit [Finite F] [Invertible (2 : F)] in
theorem normalWeights_initial (n : ℕ) (d : F) (i : Fin (n + 1)) (hi : i.val < n) :
    normalWeights n d i = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    revert hi
    refine Fin.cases (fun _ => rfl) (fun j hj => ?_) i
    exact ih j (by simpa using hj)
end Atlas.Quadratic
