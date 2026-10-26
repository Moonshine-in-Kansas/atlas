import Atlas.LinearGroups.Chevalley.Comparison.TypeCSignedMatrix
import Atlas.LinearGroups.Chevalley.WeightCompanionLeftInduction

/-! A marked homomorphism from the existing selected type-C companion to
its existing symplectic matrix model. The proof is literal form preservation
on the two signs of every simple root generator, over every commutative ring. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley.Comparison.TypeC
open Classical

theorem shortMatrix_mem (r : ℕ) (R : Type*) [CommRing R]
    (i j : Fin r) (hij : i ≠ j) (t : R) :
    shortMatrix r R i j t ∈ Matrix.symplecticGroup (Fin r) R := by
  apply _root_.SymplecticGroup.fromBlocks_mem_iff.mpr
  refine ⟨by simp, by simp, ?_⟩
  have ht : (Matrix.transvection i j t).transpose = Matrix.transvection j i t := by
    simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single]
  rw [ht]
  simpa only [Matrix.transpose_zero, zero_mul, sub_zero, add_neg_cancel,
    Matrix.transvection_zero] using
    Matrix.transvection_mul_transvection_same j i (Ne.symm hij) t (-t)

theorem longMatrix_mem (r : ℕ) (R : Type*) [CommRing R] (i : Fin r) (t : R) :
    longMatrix r R i t ∈ Matrix.symplecticGroup (Fin r) R := by
  apply _root_.SymplecticGroup.fromBlocks_mem_iff.mpr
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.transpose_single,
    mul_zero, zero_mul, one_mul, mul_one, sub_zero, and_self]

theorem longMatrix_transpose_mem (r : ℕ) (R : Type*) [CommRing R]
    (i : Fin r) (t : R) :
    (longMatrix r R i t).transpose ∈ Matrix.symplecticGroup (Fin r) R :=
  _root_.SymplecticGroup.transpose_mem (longMatrix_mem r R i t)

private theorem adjacent_ne {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

theorem weightMatrix_mem (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R]
    (g : SelectedWeightCompanion (.C (n + 1) hn) R) :
    weightMatrixHom n hn R g ∈ Matrix.symplecticGroup (Fin (n + 1)) R := by
  apply weightCompanion_induction_left (rootDatum (.C (n + 1) hn)).pairing
    (rootDatum (.C (n + 1) hn)).base (selectedWeightOrbits (.C (n + 1) hn))
    (selectedWeightOrbits_closed (.C (n + 1) hn))
    (selectedWeightOrbits_minuscule (.C (n + 1) hn)) R ?_ ?_ ?_ g
  · rw [map_one]
    exact (Matrix.symplecticGroup (Fin (n + 1)) R).one_mem
  · intro j t h hh
    obtain ⟨i, rfl⟩ := (rootDatum (.C (n + 1) hn)).indexEquiv.surjective j
    change Fin (n + 1) at i
    change weightMatrixHom n hn R
      (selectedWeightCompanionX (.C (n + 1) hn) R i t * h) ∈ _
    rw [map_mul]
    apply (Matrix.symplecticGroup (Fin (n + 1)) R).mul_mem ?_ hh
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [matrix_X_long]
      exact longMatrix_mem (n + 1) R (Fin.last n) t
    · rw [matrix_X_short]
      exact shortMatrix_mem (n + 1) R k.castSucc k.succ (adjacent_ne k) t
  · intro j t h hh
    obtain ⟨i, rfl⟩ := (rootDatum (.C (n + 1) hn)).indexEquiv.surjective j
    change Fin (n + 1) at i
    change weightMatrixHom n hn R
      (selectedWeightCompanionY (.C (n + 1) hn) R i t * h) ∈ _
    rw [map_mul]
    apply (Matrix.symplecticGroup (Fin (n + 1)) R).mul_mem ?_ hh
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [matrix_Y_long]
      exact longMatrix_transpose_mem (n + 1) R (Fin.last n) t
    · rw [matrix_Y_short]
      exact shortMatrix_mem (n + 1) R k.succ k.castSucc (Ne.symm (adjacent_ne k)) t

/-- The concrete marked comparison, with no surjectivity or kernel assertion. -/
def symplecticHom (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] :
    SelectedWeightCompanion (.C (n + 1) hn) R →* Atlas.Symplectic.Sp (n + 1) R where
  toFun g := ⟨weightMatrixHom n hn R g, weightMatrix_mem n hn R g⟩
  map_one' := Subtype.ext (map_one (weightMatrixHom n hn R))
  map_mul' g h := Subtype.ext (map_mul (weightMatrixHom n hn R) g h)

theorem symplecticHom_X_short (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R]
    (i : Fin n) (t : R) :
    (symplecticHom n hn R
      (selectedWeightCompanionX (.C (n + 1) hn) R i.castSucc t)).val =
      shortMatrix (n + 1) R i.castSucc i.succ t := matrix_X_short n hn R i t

theorem symplecticHom_Y_short (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R]
    (i : Fin n) (t : R) :
    (symplecticHom n hn R
      (selectedWeightCompanionY (.C (n + 1) hn) R i.castSucc t)).val =
      shortMatrix (n + 1) R i.succ i.castSucc t := matrix_Y_short n hn R i t

theorem symplecticHom_X_long (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] (t : R) :
    (symplecticHom n hn R
      (selectedWeightCompanionX (.C (n + 1) hn) R (Fin.last n) t)).val =
      longMatrix (n + 1) R (Fin.last n) t := matrix_X_long n hn R t

theorem symplecticHom_Y_long (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] (t : R) :
    (symplecticHom n hn R
      (selectedWeightCompanionY (.C (n + 1) hn) R (Fin.last n) t)).val =
      (longMatrix (n + 1) R (Fin.last n) t).transpose := matrix_Y_long n hn R t

theorem symplecticHom_preserves (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R]
    (g : SelectedWeightCompanion (.C (n + 1) hn) R)
    (x y : Atlas.Symplectic.Vector (n + 1) R) :
    Atlas.Symplectic.form ((symplecticHom n hn R g).val *ᵥ x)
      ((symplecticHom n hn R g).val *ᵥ y) = Atlas.Symplectic.form x y :=
  Atlas.Symplectic.preserves (symplecticHom n hn R g) x y

end Atlas.Chevalley.Comparison.TypeC
