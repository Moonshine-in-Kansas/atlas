import Atlas.Algebra.FiniteFieldBinaryRepresentation
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-! # Nondegenerate quadratic spaces of dimension at least two represent all finite odd-field values -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]

/-- The nondegenerate binary representation lemma applied to two coordinates of a diagonal form. -/
theorem weighted_units_represents {n : ℕ} (hn : 2 ≤ n) (h2 : (2 : F) ≠ 0)
    (w : Fin n → Fˣ) (c : F) :
    ∃ v : Fin n → F, QuadraticMap.weightedSumSquares F w v = c := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i,j] at this; omega
  obtain ⟨a,b,hab⟩ := Atlas.finite_field_binary_represents h2
    (w i).val (w j).val (w i).ne_zero (w j).ne_zero c
  let v : Fin n → F := fun k => if k = i then a else if k = j then b else 0
  refine ⟨v, ?_⟩
  rw [QuadraticMap.weightedSumSquares_apply]
  have he : ∀ k, w k • (v k * v k) =
      (if k = i then (w i).val * a^2 else 0) +
      (if k = j then (w j).val * b^2 else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [v, hij, pow_two, Units.smul_def]
    · by_cases hkj : k = j
      · subst k
        simp [v, hij, Ne.symm hij, pow_two, Units.smul_def]
      · simp [v, hki, hkj]
  simp_rw [he]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hab

/-- Representation of every field value by the actual quadratic form, not a chosen model. -/
theorem finite_nondegenerate_represents (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (hd : 2 ≤ Module.finrank F V) (c : F) : ∃ x : V, Q x = c := by
  letI := invertibleOfNonzero h2
  have ha : (QuadraticMap.associated (R := F) Q).SeparatingLeft := by
    intro x hx
    apply hQ.1
    intro y
    have hp := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := F) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx, mul_zero] at hp
    exact hp.symm
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' ha
  obtain ⟨v, hv⟩ := weighted_units_represents hd h2 w c
  refine ⟨e.symm v, ?_⟩
  rw [← e.map_app, e.apply_symm_apply, hv]
end Atlas.Quadratic
