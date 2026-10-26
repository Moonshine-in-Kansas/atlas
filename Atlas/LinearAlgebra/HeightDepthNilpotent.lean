import Atlas.LinearAlgebra.HeightDepth
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Nilpotent.Defs

/-! Source candidate: finite positive matrix depth is nilpotent, over any
commutative coefficient ring. Depth is closed under addition and scalars. -/

namespace Atlas.Matrix.HeightAtLeast

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem smul {S : Type*} [SMulZeroClass S R]
    {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι R}
    (hA : HeightAtLeast w d A) (s : S) : HeightAtLeast w d (s • A) := by
  intro row col h
  simp only [Matrix.smul_apply, hA row col h, smul_zero]

theorem sub {w : ι → ℤ} {d : ℤ} {A B : Matrix ι ι R}
    (hA : HeightAtLeast w d A) (hB : HeightAtLeast w d B) :
    HeightAtLeast w d (A - B) := by
  intro row col h
  simp only [Matrix.sub_apply, hA row col h, hB row col h, sub_self]

theorem pow {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι R}
    (hA : HeightAtLeast w d A) (n : ℕ) :
    HeightAtLeast w ((n : ℤ) * d) (A ^ n) := by
  induction n with
  | zero =>
    intro row col h
    have hne : row ≠ col := by intro he; subst col; omega
    simp [hne]
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hA

/-- Positive depth gives a finite nilpotence exponent even if coefficients
have torsion or zero divisors. No commutation of matrix summands is needed. -/
theorem isNilpotent_of_pos {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι R}
    (hA : HeightAtLeast w d A) (hd : 0 < d) : IsNilpotent A := by
  let B : ℕ := ∑ i, (w i).natAbs
  have hb (i : ι) : -(B : ℤ) ≤ w i ∧ w i ≤ (B : ℤ) := by
    have hi : (w i).natAbs ≤ B :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((w j).natAbs)) (Finset.mem_univ i)
    have hcast : ((w i).natAbs : ℤ) ≤ (B : ℤ) := by exact_mod_cast hi
    have hp : w i ≤ ((w i).natAbs : ℤ) := Int.le_natAbs
    have hn : -w i ≤ ((w i).natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -w i))
    omega
  refine ⟨2 * B + 1, ?_⟩
  ext row col
  apply hA.pow (2 * B + 1) row col
  have hrow := (hb row).2
  have hcol := (hb col).1
  have hd1 : (1 : ℤ) ≤ d := by omega
  have hB0 : (0 : ℤ) ≤ B := Int.natCast_nonneg _
  have hprod : 2 * (B : ℤ) + 1 ≤ (2 * (B : ℤ) + 1) * d := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hd1 (by omega : (0 : ℤ) ≤ 2 * (B : ℤ) + 1)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  omega

end Atlas.Matrix.HeightAtLeast
