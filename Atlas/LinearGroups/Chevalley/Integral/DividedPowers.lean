import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-!
# Integral divided powers on a finite root string

The raising operator on the explicit integral string basis is
`v_j ↦ (j+1) v_(j+1)`, with zero beyond the endpoint. Its divided powers
are integral operators defined by binomial coefficients. No target-ring
division, integrality assumption, or assumption about an exponential is used.

This is the ordinary root-string arithmetic provider. Identification with
Geck's root strings, the exceptional Cartan/±simple-root branches, and the
uniform root-string length bound remain separate obligations.
-/

noncomputable section

namespace Atlas.Chevalley.Integral

/-- The integral lattice of one finite string. -/
abbrev StringLattice (n : ℕ) := Fin (n + 1) →₀ ℤ

/-- String basis, extended by zero beyond its upper endpoint. -/
def stringBasis (n j : ℕ) : StringLattice n :=
  if h : j < n + 1 then Finsupp.single ⟨j, h⟩ 1 else 0

@[simp] theorem stringBasis_fin (n : ℕ) (j : Fin (n + 1)) :
    stringBasis n j.val = Finsupp.single j 1 := by
  simp [stringBasis, j.isLt]

/-- Concrete integral raising map on a truncated root string. -/
def stringRaising (n : ℕ) : Module.End ℤ (StringLattice n) :=
  Finsupp.linearCombination ℤ fun j : Fin (n + 1) =>
    ((j.val + 1 : ℕ) : ℤ) • stringBasis n (j.val + 1)

theorem stringRaising_basis (n j : ℕ) :
    stringRaising n (stringBasis n j) = (j + 1 : ℤ) • stringBasis n (j + 1) := by
  by_cases h : j < n + 1
  · simp [stringBasis, h, stringRaising]
  · have h' : ¬ j + 1 < n + 1 := by omega
    simp [stringBasis, h, h']

/-- Iteration gives the ascending factorial coefficient on the root string. -/
theorem stringRaising_pow_basis (n k j : ℕ) :
    (stringRaising n ^ k) (stringBasis n j) =
      (((j + 1).ascFactorial k : ℕ) : ℤ) • stringBasis n (j + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, stringRaising_basis, smul_smul]
    rw [Nat.ascFactorial_succ, Nat.cast_mul]
    congr 1
    push_cast
    rw [mul_comm]
    congr 1
    omega

/-- Direct integral definition; this does not divide a matrix by a factorial. -/
def stringDividedPower (n k : ℕ) : Module.End ℤ (StringLattice n) :=
  Finsupp.linearCombination ℤ fun j : Fin (n + 1) =>
    (((j.val + k).choose k : ℕ) : ℤ) • stringBasis n (j.val + k)

theorem stringDividedPower_basis (n k : ℕ) (j : Fin (n + 1)) :
    stringDividedPower n k (Finsupp.single j 1) =
      (((j.val + k).choose k : ℕ) : ℤ) • stringBasis n (j.val + k) := by
  simp [stringDividedPower]

/-- Actual divisibility of every power of the concrete integral operator. -/
theorem factorial_smul_stringDividedPower (n k : ℕ) :
    (k.factorial : ℤ) • stringDividedPower n k = stringRaising n ^ k := by
  apply Finsupp.lhom_ext
  intro j z
  have hs : Finsupp.single j z = z • Finsupp.single j (1 : ℤ) := by simp
  rw [hs, map_smul, map_smul]
  congr 1
  change (k.factorial : ℤ) • stringDividedPower n k (Finsupp.single j 1) = _
  rw [stringDividedPower_basis, ← stringBasis_fin n j, stringRaising_pow_basis, smul_smul]
  congr 1
  exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose j.val k).symm

@[simp] theorem stringDividedPower_zero (n : ℕ) :
    stringDividedPower n 0 = 1 := by
  simpa using factorial_smul_stringDividedPower n 0

@[simp] theorem stringDividedPower_one (n : ℕ) :
    stringDividedPower n 1 = stringRaising n := by
  simpa using factorial_smul_stringDividedPower n 1

/-- All divided powers beyond the endpoint vanish as integral operators. -/
theorem stringDividedPower_eq_zero (n k : ℕ) (hk : n < k) :
    stringDividedPower n k = 0 := by
  apply Finsupp.lhom_ext
  intro j z
  have h : ¬ j.val + k < n + 1 := by omega
  simp [stringDividedPower, stringBasis, h]

/-- The concrete raising operator is nilpotent at the actual string length. -/
theorem stringRaising_pow_eq_zero (n k : ℕ) (hk : n < k) :
    stringRaising n ^ k = 0 := by
  rw [← factorial_smul_stringDividedPower, stringDividedPower_eq_zero n k hk, smul_zero]

theorem stringRaising_nilpotent (n : ℕ) : IsNilpotent (stringRaising n) :=
  ⟨n + 1, stringRaising_pow_eq_zero n (n + 1) (Nat.lt_succ_self n)⟩

/-- Every power has a genuine integral divided-power witness. -/
theorem stringRaising_integral_divided_powers (n k : ℕ) :
    ∃ D : Module.End ℤ (StringLattice n), (k.factorial : ℤ) • D = stringRaising n ^ k :=
  ⟨stringDividedPower n k, factorial_smul_stringDividedPower n k⟩

end Atlas.Chevalley.Integral
