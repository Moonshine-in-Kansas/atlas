import Atlas.LinearGroups.Chevalley.Comparison.TypeCWeightBlock
import Atlas.LinearGroups.Symplectic.Basic

/-! A diagonal sign change converts the pinned minuscule coefficients into
standard symplectic elementary matrices. All calculations are over CommRing. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeC
open Classical ClassicalData Integral.Minuscule
open scoped Matrix

/-- The negative coordinate has sign determined by its distance from the long end. -/
def frameSign (n : ℕ) (R : Type*) [CommRing R] : Index (n + 1) → R
  | .inl _ => 1
  | .inr k => (-1) ^ (n - k.val)

private theorem frameSign_square (n : ℕ) (R : Type*) [CommRing R] (k : Index (n + 1)) :
    frameSign n R k * frameSign n R k = 1 := by
  cases k with
  | inl k => simp [frameSign]
  | inr k => simp only [frameSign, ← mul_pow, neg_mul_neg, one_mul, one_pow]

private theorem frameSign_adjacent (n : ℕ) (R : Type*) [CommRing R] (i : Fin n) :
    frameSign n R (.inr i.castSucc) * frameSign n R (.inr i.succ) = -1 := by
  have he : n - i.val = n - (i.val + 1) + 1 := by omega
  have hs := frameSign_square n R (.inr i.succ)
  simp only [frameSign, Fin.val_succ] at hs
  simp only [frameSign, Fin.val_castSucc, Fin.val_succ, he, pow_succ]
  calc
    _ = -((-1 : R) ^ (n - (i.val + 1)) * (-1) ^ (n - (i.val + 1))) := by ring
    _ = -1 := by rw [hs]

private def frame (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (Index (n + 1)) (Index (n + 1)) R := Matrix.diagonal (frameSign n R)

private theorem frame_square (n : ℕ) (R : Type*) [CommRing R] :
    frame n R * frame n R = 1 := by
  rw [frame, Matrix.diagonal_mul_diagonal]
  simp only [frameSign_square]
  exact Matrix.diagonal_one

def twist (n : ℕ) (R : Type*) [CommRing R]
    (A : Matrix (Index (n + 1)) (Index (n + 1)) R) :
    Matrix (Index (n + 1)) (Index (n + 1)) R := frame n R * A * frame n R

def twistHom (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (Index (n + 1)) (Index (n + 1)) R →*
      Matrix (Index (n + 1)) (Index (n + 1)) R where
  toFun := twist n R
  map_one' := by simp only [twist, mul_one, frame_square]
  map_mul' A B := by
    change frame n R * (A * B) * frame n R =
      (frame n R * A * frame n R) * (frame n R * B * frame n R)
    calc
      _ = frame n R * A * (frame n R * frame n R) * B * frame n R := by
        rw [frame_square]
        simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]

private theorem twist_add (n : ℕ) (R : Type*) [CommRing R]
    (A B : Matrix (Index (n + 1)) (Index (n + 1)) R) :
    twist n R (A + B) = twist n R A + twist n R B := by
  simp only [twist, mul_add, add_mul]

private theorem twist_smul (n : ℕ) (R : Type*) [CommRing R] (t : R)
    (A : Matrix (Index (n + 1)) (Index (n + 1)) R) :
    twist n R (t • A) = t • twist n R A := by
  simp only [twist, Matrix.mul_smul, Matrix.smul_mul]

private theorem twist_single (n : ℕ) (R : Type*) [CommRing R]
    (i j : Index (n + 1)) (t : R) :
    twist n R (Matrix.single i j t) =
      Matrix.single i j (frameSign n R i * t * frameSign n R j) := by
  ext a b
  simp only [twist, frame, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases ha : i = a <;> by_cases hb : j = b <;>
    simp [Matrix.single_apply, ha, hb]

def weightMatrixHom (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] :
    SelectedWeightCompanion (.C (n + 1) hn) R →*
      Matrix (Index (n + 1)) (Index (n + 1)) R :=
  (twistHom n R).comp (rawMatrixHom n hn R)

/-- Paired elementary matrices in the established symplectic coordinate order. -/
def shortMatrix (r : ℕ) (R : Type*) [CommRing R] (i j : Fin r) (t : R) :
    Matrix (Index r) (Index r) R :=
  Matrix.fromBlocks (Matrix.transvection i j t) 0 0 (Matrix.transvection j i (-t))

def longMatrix (r : ℕ) (R : Type*) [CommRing R] (i : Fin r) (t : R) :
    Matrix (Index r) (Index r) R :=
  Matrix.fromBlocks 1 (Matrix.single i i t) 0 1

private theorem adjacent_ne {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at h'
  omega

private theorem simple_pair (n : ℕ) (i : Fin n) :
    simpleB n i.castSucc = longRoot true i.castSucc i.succ (adjacent_ne i)
      1 (-1) (Or.inl rfl) (Or.inr rfl) := by
  simp only [simpleB, Fin.val_castSucc, i.isLt, dite_true]
  rfl

private theorem simple_axis (n : ℕ) :
    simpleB n (Fin.last n) = shortRoot (Fin.last n) 1 (Or.inl rfl) := by
  simp only [simpleB, Fin.val_last, lt_self_iff_false, dite_false]

private theorem twist_pair (n : ℕ) (R : Type*) [CommRing R] (i : Fin n) :
    twist n R (Matrix.single (.inl i.castSucc) (.inl i.succ) 1 +
      Matrix.single (.inr i.succ) (.inr i.castSucc) 1) =
    Matrix.single (.inl i.castSucc) (.inl i.succ) 1 +
      Matrix.single (.inr i.succ) (.inr i.castSucc) (-1) := by
  rw [twist_add, twist_single, twist_single]
  have hs : frameSign n R (.inr i.succ) * frameSign n R (.inr i.castSucc) = -1 := by
    simpa only [mul_comm] using frameSign_adjacent n R i
  simpa only [frameSign, one_mul, mul_one] using
    congrArg (fun z : R => (Matrix.single (.inl i.castSucc) (.inl i.succ) 1 +
      Matrix.single (.inr i.succ) (.inr i.castSucc) z :
        Matrix (Index (n + 1)) (Index (n + 1)) R)) hs

private theorem twist_pair_reverse (n : ℕ) (R : Type*) [CommRing R] (i : Fin n) :
    twist n R (Matrix.single (.inl i.succ) (.inl i.castSucc) 1 +
      Matrix.single (.inr i.castSucc) (.inr i.succ) 1) =
    Matrix.single (.inl i.succ) (.inl i.castSucc) 1 +
      Matrix.single (.inr i.castSucc) (.inr i.succ) (-1) := by
  rw [twist_add, twist_single, twist_single]
  simpa only [frameSign, one_mul, mul_one] using
    congrArg (fun z : R => (Matrix.single (.inl i.succ) (.inl i.castSucc) 1 +
      Matrix.single (.inr i.castSucc) (.inr i.succ) z :
        Matrix (Index (n + 1)) (Index (n + 1)) R)) (frameSign_adjacent n R i)

theorem matrix_X_short (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R]
    (i : Fin n) (t : R) :
    weightMatrixHom n hn R (selectedWeightCompanionX (.C (n + 1) hn) R i.castSucc t) =
      shortMatrix (n + 1) R i.castSucc i.succ t := by
  change twist n R (reindex (n + 1) R
    ((Integral.Minuscule.TypeC.actualStrings (n + 1)).rootMatrix R (simpleB n i.castSucc) (-1) t)) = _
  rw [Strings.rootMatrix, map_add, map_one, map_smul, simple_pair, raising_pair,
    twist_add, twist_smul, twist_pair]
  have ho : twist n R (1 : Matrix (Index (n + 1)) (Index (n + 1)) R) = 1 :=
    (twistHom n R).map_one
  rw [ho]
  ext a b
  cases a <;> cases b <;>
    simp [shortMatrix, Matrix.transvection, Matrix.fromBlocks, Matrix.single_apply,
      Matrix.one_apply, smul_eq_mul, mul_add, eq_comm]

theorem matrix_Y_short (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R]
    (i : Fin n) (t : R) :
    weightMatrixHom n hn R (selectedWeightCompanionY (.C (n + 1) hn) R i.castSucc t) =
      shortMatrix (n + 1) R i.succ i.castSucc t := by
  change twist n R (reindex (n + 1) R
    ((Integral.Minuscule.TypeC.actualStrings (n + 1)).rootMatrix R (simpleB n i.castSucc) 1 t)) = _
  rw [Strings.rootMatrix, map_add, map_one, map_smul, simple_pair, lowering_pair,
    twist_add, twist_smul, twist_pair_reverse]
  have ho : twist n R (1 : Matrix (Index (n + 1)) (Index (n + 1)) R) = 1 :=
    (twistHom n R).map_one
  rw [ho]
  ext a b
  cases a <;> cases b <;>
    simp [shortMatrix, Matrix.transvection, Matrix.fromBlocks, Matrix.single_apply,
      Matrix.one_apply, smul_eq_mul, mul_add, eq_comm]

theorem matrix_X_long (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] (t : R) :
    weightMatrixHom n hn R (selectedWeightCompanionX (.C (n + 1) hn) R (Fin.last n) t) =
      longMatrix (n + 1) R (Fin.last n) t := by
  change twist n R (reindex (n + 1) R
    ((Integral.Minuscule.TypeC.actualStrings (n + 1)).rootMatrix R (simpleB n (Fin.last n)) (-1) t)) = _
  rw [Strings.rootMatrix, map_add, map_one, map_smul, simple_axis, raising_axis,
    twist_add, twist_smul, twist_single]
  have ho : twist n R (1 : Matrix (Index (n + 1)) (Index (n + 1)) R) = 1 :=
    (twistHom n R).map_one
  rw [ho]
  ext a b
  cases a <;> cases b <;>
    simp [frameSign, longMatrix, Matrix.fromBlocks, Matrix.single_apply,
      Matrix.one_apply, smul_eq_mul, eq_comm]

theorem matrix_Y_long (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] (t : R) :
    weightMatrixHom n hn R (selectedWeightCompanionY (.C (n + 1) hn) R (Fin.last n) t) =
      (longMatrix (n + 1) R (Fin.last n) t).transpose := by
  change twist n R (reindex (n + 1) R
    ((Integral.Minuscule.TypeC.actualStrings (n + 1)).rootMatrix R (simpleB n (Fin.last n)) 1 t)) = _
  rw [Strings.rootMatrix, map_add, map_one, map_smul, simple_axis, lowering_axis,
    twist_add, twist_smul, twist_single]
  have ho : twist n R (1 : Matrix (Index (n + 1)) (Index (n + 1)) R) = 1 :=
    (twistHom n R).map_one
  rw [ho]
  ext a b
  cases a <;> cases b <;>
    simp [frameSign, longMatrix, Matrix.transpose_apply, Matrix.fromBlocks,
      Matrix.single_apply, Matrix.one_apply, smul_eq_mul, eq_comm, and_comm]

end Atlas.Chevalley.Comparison.TypeC
