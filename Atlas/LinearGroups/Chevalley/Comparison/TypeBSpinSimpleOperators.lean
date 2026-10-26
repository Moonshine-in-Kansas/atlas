import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinShortOperators
import Atlas.LinearAlgebra.BooleanSpinOperators

/-! The actual integral B minuscule normalization agrees with the Boolean spin CAR
operators. Adjacent long generators have no extra sign; the short endpoint uses parity. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule Atlas.BooleanSpin
open scoped Matrix

private theorem long_grade (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) (σ : SpinIndex n) :
    (Integral.Minuscule.TypeB.actualStrings n).pairing
      (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (spinLabel n σ) =
      Integral.Minuscule.TypeB.halfDifference (σ i) (σ j) := by
  change Integral.Minuscule.TypeB.spinWeight n σ
    (corootElement (pairingB (n+1)) (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl))) = _
  have h := Integral.Minuscule.TypeB.twice_spinWeight_long_pairing n σ i j hij
    1 (-1) (Or.inl rfl) (Or.inr rfl)
  cases hi : σ i <;> cases hj : σ j <;>
    simp [Integral.Minuscule.TypeB.halfDifference, Integral.Minuscule.TypeB.sign, hi, hj] at h ⊢ <;> omega

private theorem long_reflection (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) (σ : SpinIndex n) :
    (Integral.Minuscule.TypeB.actualStrings n).reflection
      (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (spinLabel n σ) =
      spinLabel n (Function.update (Function.update σ j (σ i)) i (σ j)) := by
  apply Subtype.ext
  change weightReflection (pairingB (n+1)) _ (Integral.Minuscule.TypeB.spinWeight n σ) = _
  rw [Integral.Minuscule.TypeB.spinWeight_reflection]
  apply congrArg (Integral.Minuscule.TypeB.spinWeight n)
  funext k
  by_cases hi : k=i <;> by_cases hj : k=j <;>
    cases hσi : σ i <;> cases hσj : σ j <;> cases hσk : σ k <;>
    simp_all [Integral.Minuscule.TypeB.reflectedSigns,
      Integral.Minuscule.TypeB.reflect_long_coordinates,
      Integral.Minuscule.TypeB.signVector, Integral.Minuscule.TypeB.sign]

theorem spin_raising_simple_long (n : ℕ) (R : Type*) [CommRing R] (i : Fin n) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n i.castSucc) (-1)) =
      matrix R (creation R i.castSucc) * matrix R (annihilation R i.succ) := by
  have hij : i.castSucc < i.succ := i.castSucc_lt_succ
  have hne : i.castSucc ≠ i.succ := ne_of_lt hij
  have hs : simpleB n i.castSucc =
      longRoot true i.castSucc i.succ hne 1 (-1) (Or.inl rfl) (Or.inr rfl) := by
    simp [simpleB, i.isLt]
    rfl
  rw [hs, ← map_mul]
  ext σ τ
  change (Integral.Minuscule.TypeB.actualStrings n).stepMatrix R _ (-1)
    (spinLabel n σ) (spinLabel n τ) = _
  rw [Strings.stepMatrix_entry, long_grade, long_reflection, matrix_apply]
  simp only [(spinLabel_injective n).eq_iff]
  simp only [Module.End.mul_apply, creation_annihilation_adjacent_single]
  cases hi : τ i.castSucc <;> cases hj : τ i.succ <;>
    simp [Integral.Minuscule.TypeB.halfDifference, hi, hj, Finsupp.single_apply, eq_comm]

theorem spin_lowering_simple_long (n : ℕ) (R : Type*) [CommRing R] (i : Fin n) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n i.castSucc) 1) =
      matrix R (creation R i.succ) * matrix R (annihilation R i.castSucc) := by
  have hij : i.castSucc < i.succ := i.castSucc_lt_succ
  have hne : i.castSucc ≠ i.succ := ne_of_lt hij
  have hs : simpleB n i.castSucc =
      longRoot true i.castSucc i.succ hne 1 (-1) (Or.inl rfl) (Or.inr rfl) := by
    simp [simpleB, i.isLt]
    rfl
  rw [hs, ← map_mul]
  ext σ τ
  change (Integral.Minuscule.TypeB.actualStrings n).stepMatrix R _ 1
    (spinLabel n σ) (spinLabel n τ) = _
  rw [Strings.stepMatrix_entry, long_grade, long_reflection, matrix_apply]
  simp only [(spinLabel_injective n).eq_iff]
  simp only [Module.End.mul_apply, creation_annihilation_adjacent_reverse_single]
  cases hi : τ i.castSucc <;> cases hj : τ i.succ <;>
    simp [Integral.Minuscule.TypeB.halfDifference, hi, hj, Finsupp.single_apply, eq_comm]

theorem spin_raising_simple_last (n : ℕ) (R : Type*) [CommRing R] :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n (Fin.last n)) (-1)) =
      matrix R (creation R (Fin.last n)) * matrix R (parity (I := Fin (n+1)) R) := by
  have hs : simpleB n (Fin.last n) = shortRoot (Fin.last n) 1 (Or.inl rfl) := by simp [simpleB]
  rw [hs, spin_raising_short, ← map_mul]
  ext σ τ
  rw [matrix_apply]
  simp only [Module.End.mul_apply, creation_parity_last_single]
  cases h : τ (Fin.last n) <;> simp [h, Finsupp.single_apply, eq_comm]

theorem spin_lowering_simple_last (n : ℕ) (R : Type*) [CommRing R] :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n (Fin.last n)) 1) =
      matrix R (parity (I := Fin (n+1)) R) * matrix R (annihilation R (Fin.last n)) := by
  have hs : simpleB n (Fin.last n) = shortRoot (Fin.last n) 1 (Or.inl rfl) := by simp [simpleB]
  rw [hs, spin_lowering_short, ← map_mul]
  ext σ τ
  rw [matrix_apply]
  simp only [Module.End.mul_apply, parity_annihilation_last_single]
  cases h : τ (Fin.last n) <;> simp [h, Finsupp.single_apply, eq_comm]

end Atlas.Chevalley.Comparison.TypeB
