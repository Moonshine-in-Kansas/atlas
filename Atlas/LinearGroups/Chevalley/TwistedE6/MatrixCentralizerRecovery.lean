import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
Source-only coefficient recovery for matrix centralizers. The three
exponents are 1, q, q+1, with 2 <= q and q+1 < |K|. No inverse of a matrix,
division by a scalar, nilpotence, or commutation of the coefficient matrices
is required. In particular the result applies when |K| = q^2, including q=2.
This file makes no statement about the center of a fixed subgroup.
-/
noncomputable section
namespace Atlas.LinearAlgebra.MatrixCentralizer
open Polynomial
open scoped Matrix

section Coefficients
variable {K : Type*} [Field K] [Finite K]

/-- Root counting separates the three distinct monomials even over the
smallest quadratic finite field. The cardinality bound is explicit. -/
theorem scalar_coefficients_eq_zero {q : ℕ} (hq : 2 ≤ q)
    (hsize : q + 1 < Nat.card K) (a b c : K)
    (h : ∀ u : K, u * a + u ^ q * b + u ^ (q + 1) * c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let p : K[X] := monomial 1 a + monomial q b + monomial (q + 1) c
  have hdeg : p.natDegree ≤ q + 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_monomial_le a).trans (by omega)
      · exact (Polynomial.natDegree_monomial_le b).trans (by omega)
    · exact Polynomial.natDegree_monomial_le c
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := id) Function.injective_id
    · intro u
      simpa only [p, Polynomial.eval_add, Polynomial.eval_monomial,
        pow_one, id_eq, mul_comm] using h u
    · rw [← Nat.card_eq_fintype_card]
      exact hdeg.trans_lt hsize
  have hq0 : q ≠ 0 := by omega
  have hq1 : q ≠ 1 := by omega
  have hq11 : q + 1 ≠ 1 := by omega
  have hnext : q + 1 ≠ q := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa [p, Polynomial.coeff_monomial, hq0, hq1, hq11] using
      congrArg (fun f : K[X] => f.coeff 1) hp
  · simpa [p, Polynomial.coeff_monomial, Ne.symm hq1, hnext] using
      congrArg (fun f : K[X] => f.coeff q) hp
  · simpa [p, Polynomial.coeff_monomial, hq0, Ne.symm hq11, Ne.symm hnext] using
      congrArg (fun f : K[X] => f.coeff (q + 1)) hp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All three coefficients can be arbitrary matrices. The last coefficient
need not be A*B, and g need not be invertible. -/
theorem commute_coefficients_of_polynomial {q : ℕ} (hq : 2 ≤ q)
    (hsize : q + 1 < Nat.card K) (g A B D : Matrix n n K)
    (h : ∀ u : K,
      Commute g (1 + u • A + u ^ q • B + u ^ (q + 1) • D)) :
    Commute g A ∧ Commute g B ∧ Commute g D := by
  have hz (u : K) :
      u • (g * A - A * g) + u ^ q • (g * B - B * g) +
        u ^ (q + 1) • (g * D - D * g) = 0 := by
    calc
      _ = g * (1 + u • A + u ^ q • B + u ^ (q + 1) • D) -
          (1 + u • A + u ^ q • B + u ^ (q + 1) • D) * g := by
        simp only [mul_add, add_mul, mul_one, one_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr (h u).eq
  have hc (r s : n) :
      (g * A - A * g) r s = 0 ∧ (g * B - B * g) r s = 0 ∧
        (g * D - D * g) r s = 0 := by
    apply scalar_coefficients_eq_zero hq hsize
    intro u
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] using congrArg (fun M : Matrix n n K => M r s) (hz u)
  refine ⟨?_, ?_, ?_⟩
  · change g * A = A * g
    apply sub_eq_zero.mp
    ext r s
    exact (hc r s).1
  · change g * B = B * g
    apply sub_eq_zero.mp
    ext r s
    exact (hc r s).2.1
  · change g * D = D * g
    apply sub_eq_zero.mp
    ext r s
    exact (hc r s).2.2

/-- The strict inequality is valid at q=2, where it reads 3<4. -/
theorem succ_lt_square {q : ℕ} (hq : 2 ≤ q) : q + 1 < q ^ 2 := by
  have hm : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  calc
    q + 1 < 2 * q := by omega
    _ ≤ q * q := hm
    _ = q ^ 2 := (pow_two q).symm

/-- The requested quadratic-field cardinality specialization. -/
theorem commute_pair_of_card_square {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card K = q ^ 2) (g A B : Matrix n n K)
    (h : ∀ u : K,
      Commute g (1 + u • A + u ^ q • B + u ^ (q + 1) • (A * B))) :
    Commute g A ∧ Commute g B := by
  have hs : q + 1 < Nat.card K := by
    rw [hcard]
    exact succ_lt_square hq
  have hc := commute_coefficients_of_polynomial hq hs g A B (A * B) h
  exact ⟨hc.1, hc.2.1⟩

end Coefficients

section Affine
variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Ordered multiplication alone gives the cross coefficient A*B. No
commutation or square-zero hypothesis is needed for this expansion. -/
theorem affine_pair_expansion (A B : Matrix n n R) (u v : R) :
    (1 + u • A) * (1 + v • B) =
      1 + u • A + v • B + (u * v) • (A * B) := by
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  abel

theorem frobenius_pair_expansion (A B : Matrix n n R) (q : ℕ) (u : R) :
    (1 + u • A) * (1 + u ^ q • B) =
      1 + u • A + u ^ q • B + u ^ (q + 1) • (A * B) := by
  rw [affine_pair_expansion]
  have hp : u * u ^ q = u ^ (q + 1) := by rw [pow_succ, mul_comm]
  rw [hp]

/-- One fixed-root value at parameter 1 recovers its affine coefficient. -/
theorem commute_of_one_add (g A : Matrix n n R) (h : Commute g (1 + A)) :
    Commute g A := by
  have he := h.eq
  simp only [mul_add, add_mul, mul_one, one_mul] at he
  exact add_left_cancel he

/-- Once its coefficient commutes, every parameter of the split root does. -/
theorem commute_affine (g A : Matrix n n R) (h : Commute g A) (t : R) :
    Commute g (1 + t • A) := by
  change g * (1 + t • A) = (1 + t • A) * g
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  rw [h.eq]

end Affine

section FiniteField
variable {K n : Type*} [Field K] [Finite K] [Fintype n] [DecidableEq n]

/-- Direct interface for an ordered pair of affine root matrices. Square
zero and orthogonality belong to the root provider, not to this recovery. -/
theorem commute_pair_of_affine_product {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card K = q ^ 2) (g A B : Matrix n n K)
    (h : ∀ u : K, Commute g ((1 + u • A) * (1 + u ^ q • B))) :
    Commute g A ∧ Commute g B := by
  apply commute_pair_of_card_square hq hcard g A B
  intro u
  simpa only [frobenius_pair_expansion] using h u

end FiniteField
end Atlas.LinearAlgebra.MatrixCentralizer
