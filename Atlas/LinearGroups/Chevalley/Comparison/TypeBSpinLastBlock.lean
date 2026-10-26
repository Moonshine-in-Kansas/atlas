import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinShortOperators
import Atlas.LinearAlgebra.OddRankOneSpinMatrix
import Mathlib.Data.Fin.Tuple.Basic

/-! The terminal short-root matrix is an actual direct sum of identical two-dimensional
blocks. Occupied precedes empty, agreeing with the odd rank-one spin matrix convention. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule
open scoped Matrix

theorem spin_X_last_block (n : ℕ) (R : Type*) [CommRing R]
    (σ : Fin n → Bool) (t : R) :
    (fun a b : Fin 2 => spinReindex n R
      ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (shortRoot (Fin.last n) 1 (Or.inl rfl)) (-1) t)
      (Fin.snoc σ (![true, false] a)) (Fin.snoc σ (![true, false] b))) =
      Atlas.OddRankOneSpinMatrix.upper t := by
  ext a b
  rw [spin_X_short_entry]
  fin_cases a <;> fin_cases b <;>
    simp [Fin.update_snoc_last, Fin.snoc_inj, Atlas.OddRankOneSpinMatrix.upper]

theorem spin_Y_last_block (n : ℕ) (R : Type*) [CommRing R]
    (σ : Fin n → Bool) (t : R) :
    (fun a b : Fin 2 => spinReindex n R
      ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (shortRoot (Fin.last n) 1 (Or.inl rfl)) 1 t)
      (Fin.snoc σ (![true, false] a)) (Fin.snoc σ (![true, false] b))) =
      Atlas.OddRankOneSpinMatrix.lower t := by
  ext a b
  rw [spin_Y_short_entry]
  fin_cases a <;> fin_cases b <;>
    simp [Fin.update_snoc_last, Fin.snoc_inj, Atlas.OddRankOneSpinMatrix.lower]

theorem spin_X_last_offBlock (n : ℕ) (R : Type*) [CommRing R]
    (σ τ : Fin n → Bool) (hστ : σ ≠ τ) (a b : Bool) (t : R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (shortRoot (Fin.last n) 1 (Or.inl rfl)) (-1) t)
      (Fin.snoc σ a) (Fin.snoc τ b) = 0 := by
  rw [spin_X_short_entry]
  simp [Fin.update_snoc_last, Fin.snoc_inj, hστ, Ne.symm hστ]

theorem spin_Y_last_offBlock (n : ℕ) (R : Type*) [CommRing R]
    (σ τ : Fin n → Bool) (hστ : σ ≠ τ) (a b : Bool) (t : R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (shortRoot (Fin.last n) 1 (Or.inl rfl)) 1 t)
      (Fin.snoc σ a) (Fin.snoc τ b) = 0 := by
  rw [spin_Y_short_entry]
  simp [Fin.update_snoc_last, Fin.snoc_inj, hστ, Ne.symm hστ]

end Atlas.Chevalley.Comparison.TypeB
