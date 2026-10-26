import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Subgroup.Basic
import Lean.Elab.Tactic.Omega

/-! Unitriangularity relative to an integer height, with no chosen total
ordering of equal-height indices. The generic statements use no root data. -/

namespace Atlas.Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- At entries where row height is at most column height, the matrix agrees with the identity. Every
nonidentity matrix entry strictly increases height from column to row. -/
def HeightUnitriangular (w : ι → ℤ) (A : Matrix ι ι R) : Prop :=
  ∀ i j, w i ≤ w j → A i j = (1 : Matrix ι ι R) i j

namespace HeightUnitriangular

theorem one (w : ι → ℤ) : HeightUnitriangular w (1 : Matrix ι ι R) :=
  fun _ _ _ => rfl

theorem diagonal {w : ι → ℤ} {A : Matrix ι ι R}
    (hA : HeightUnitriangular w A) (i : ι) : A i i = 1 := by
  simpa using hA i i le_rfl

theorem mul {w : ι → ℤ} {A B : Matrix ι ι R}
    (hA : HeightUnitriangular w A) (hB : HeightUnitriangular w B) :
    HeightUnitriangular w (A * B) := by
  intro i j hij
  have hterm (k : ι) :
      A i k * B k j = (1 : Matrix ι ι R) i k * (1 : Matrix ι ι R) k j := by
    by_cases hik : i = k
    · subst k
      rw [hA i i le_rfl, hB i j hij]
    by_cases hkj : k = j
    · subst k
      rw [hA i j hij, hB j j le_rfl]
    by_cases hi : w i ≤ w k
    · rw [hA i k hi]
      simp [Matrix.one_apply, hik]
    · have hj : w k ≤ w j := by omega
      rw [hB k j hj]
      simp [Matrix.one_apply, hkj]
  calc
    (A * B) i j = ((1 : Matrix ι ι R) * 1 : Matrix ι ι R) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => hterm k)
    _ = (1 : Matrix ι ι R) i j := by simp

theorem pow {w : ι → ℤ} {A : Matrix ι ι R}
    (hA : HeightUnitriangular w A) (n : ℕ) : HeightUnitriangular w (A ^ n) := by
  induction n with
  | zero => simpa using one w
  | succ n ih => simpa only [pow_succ] using ih.mul hA

/-- A height-unitriangular matrix which is also diagonal is the identity. -/
theorem eq_one_of_offDiagonal_zero {w : ι → ℤ} {A : Matrix ι ι R}
    (hA : HeightUnitriangular w A) (hdiag : ∀ i j, i ≠ j → A i j = 0) :
    A = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hA.diagonal i
  · simp [hdiag i j hij, Matrix.one_apply, hij]

end HeightUnitriangular

/-- Height-unitriangular units, recording the same property for their inverse.
This definition needs no field or characteristic hypothesis. -/
def heightUnitriangularSubgroup (w : ι → ℤ) : Subgroup (Matrix ι ι R)ˣ where
  carrier := {g | HeightUnitriangular w g.val ∧ HeightUnitriangular w g.inv}
  one_mem' := ⟨HeightUnitriangular.one w, HeightUnitriangular.one w⟩
  mul_mem' {a b} ha hb := ⟨ha.1.mul hb.1, hb.2.mul ha.2⟩
  inv_mem' {a} ha := ⟨ha.2, ha.1⟩

end Atlas.Matrix
