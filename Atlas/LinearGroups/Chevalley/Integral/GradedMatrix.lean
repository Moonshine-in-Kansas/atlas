import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

/-! Integral support degrees persist through divided powers, before reduction
to an arbitrary coefficient ring. No factorial is cancelled in that ring. -/
noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every nonzero entry has the specified difference of integer weights. -/
def WeightedSupport (w : ι → ℤ) (d : ℤ) (A : Matrix ι ι ℤ) : Prop :=
  ∀ i j, A i j ≠ 0 → w i = w j + d

namespace WeightedSupport

/-- A diagonal commutator identity over the integers gives exact support degrees. -/
theorem of_diagonal_commutator {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι ℤ}
    (h : Matrix.diagonal w * A - A * Matrix.diagonal w = d • A) :
    WeightedSupport w d A := by
  intro i j hij
  have he := congrArg (fun B : Matrix ι ι ℤ => B i j) h
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul] at he
  have hz : (w i - (w j+d)) * A i j = 0 := by nlinarith [he]
  have hw := (mul_eq_zero.mp hz).resolve_right hij
  omega

omit [Fintype ι] in
theorem one (w : ι → ℤ) : WeightedSupport w 0 (1 : Matrix ι ι ℤ) := by
  intro i j hij
  have he : i = j := by
    by_contra h
    simp [h] at hij
  simp [he]

omit [DecidableEq ι] in
theorem mul {w : ι → ℤ} {a b : ℤ} {A B : Matrix ι ι ℤ}
    (hA : WeightedSupport w a A) (hB : WeightedSupport w b B) :
    WeightedSupport w (a+b) (A*B) := by
  intro i j hij
  obtain ⟨k, hk⟩ : ∃ k, A i k * B k j ≠ 0 := by
    by_contra h
    push Not at h
    apply hij
    simp [Matrix.mul_apply, h]
  obtain ⟨ha,hb⟩ := mul_ne_zero_iff.mp hk
  have hwA := hA i k ha
  have hwB := hB k j hb
  omega

theorem pow {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι ℤ}
    (hA : WeightedSupport w d A) (n : ℕ) :
    WeightedSupport w ((n : ℤ)*d) (A^n) := by
  induction n with
  | zero => simpa using one w
  | succ n ih =>
    simpa [pow_succ, Nat.cast_add, Nat.cast_one, add_mul] using ih.mul hA

omit [Fintype ι] [DecidableEq ι] in
/-- Cancellation is only in the integral source matrix. -/
theorem of_smul {w : ι → ℤ} {d c : ℤ} {A D : Matrix ι ι ℤ}
    (hA : WeightedSupport w d A) (hc : c ≠ 0) (h : c • D = A) :
    WeightedSupport w d D := by
  intro i j hij
  apply hA i j
  rw [← h]
  change c * D i j ≠ 0
  exact mul_ne_zero hc hij

theorem divided {w : ι → ℤ} {d : ℤ} {A D : Matrix ι ι ℤ}
    (hA : WeightedSupport w d A) (n : ℕ)
    (hD : (n.factorial : ℤ) • D = A^n) :
    WeightedSupport w ((n : ℤ)*d) D :=
  (hA.pow n).of_smul (by exact_mod_cast Nat.factorial_ne_zero n) hD

/-- The actual diagonal weight matrix conjugates every homogeneous integral
matrix after reduction, in any commutative ring. -/
theorem diagonal_mul_map (R : Type*) [CommRing R]
    {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι ℤ}
    (hA : WeightedSupport w d A) (t : Rˣ) :
    Matrix.diagonal (fun i => (t ^ w i).val) * A.map (Int.castRingHom R) =
      (t^d).val • (A.map (Int.castRingHom R) *
        Matrix.diagonal (fun i => (t ^ w i).val)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal,
    Matrix.map_apply, smul_eq_mul]
  by_cases hij : A i j = 0
  · simp [hij]
  · rw [hA i j hij, zpow_add, Units.val_mul]
    ring

end WeightedSupport
end Atlas.Chevalley.Integral
