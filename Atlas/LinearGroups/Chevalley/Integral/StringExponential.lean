import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Polynomial.DegreeLT
import Atlas.LinearGroups.Chevalley.Integral.DividedPowers
import Mathlib.Algebra.Module.Torsion.Free

noncomputable section
open scoped Polynomial
namespace Atlas.Chevalley.Integral

theorem stringDividedPower_mul (n k l : ℕ) :
    stringDividedPower n k * stringDividedPower n l =
      (((k + l).choose l : ℕ) : ℤ) • stringDividedPower n (k + l) := by
  have hsc : (k.factorial : ℤ) * (l.factorial : ℤ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
      (by exact_mod_cast Nat.factorial_ne_zero l)
  apply (smul_right_injective (M := Module.End ℤ (StringLattice n)) hsc)
  calc
    ((k.factorial : ℤ) * (l.factorial : ℤ)) •
        (stringDividedPower n k * stringDividedPower n l) =
        ((k.factorial : ℤ) • stringDividedPower n k) *
        ((l.factorial : ℤ) • stringDividedPower n l) := by
      rw [smul_mul_smul_comm]
    _ = stringRaising n ^ k * stringRaising n ^ l := by
      rw [factorial_smul_stringDividedPower, factorial_smul_stringDividedPower]
    _ = stringRaising n ^ (k + l) := (pow_add _ _ _).symm
    _ = ((k + l).factorial : ℤ) • stringDividedPower n (k + l) :=
      (factorial_smul_stringDividedPower n (k + l)).symm
    _ = _ := by
      dsimp only
      rw [smul_smul]
      congr 1
      exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Nat.add_choose_mul_factorial_mul_factorial k l).symm)
end Atlas.Chevalley.Integral

namespace Atlas.Chevalley.Integral
variable {R : Type*} [CommRing R]

/-- The concrete binomial exponential is the transpose of finite polynomial translation. -/
noncomputable def stringExponential (n : ℕ) (t : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  (LinearMap.toMatrix (Polynomial.degreeLT.basis R (n+1))
    (Polynomial.degreeLT.basis R (n+1))
    (Polynomial.taylorLinearEquiv t (n+1)).toLinearMap).transpose

theorem stringExponential_entry (n : ℕ) (t : R) (i j : Fin (n+1)) :
    stringExponential n t i j = t ^ (i.val - j.val) * (i.val.choose j.val : R) := by
  rw [stringExponential, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    Polynomial.degreeLT.basis_repr]
  change (Polynomial.taylor t ((Polynomial.degreeLT.basis R (n+1) i) : R[X])).coeff j = _
  rw [Polynomial.degreeLT.basis_val, Polynomial.taylor_X_pow, Polynomial.coeff_X_add_C_pow]

theorem stringExponential_add (n : ℕ) (s t : R) :
    stringExponential n (s+t) = stringExponential n s * stringExponential n t := by
  have h : (Polynomial.taylorLinearEquiv (s+t) (n+1)).toLinearMap =
      (Polynomial.taylorLinearEquiv t (n+1)).toLinearMap *
      (Polynomial.taylorLinearEquiv s (n+1)).toLinearMap := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change Polynomial.taylor (s+t) (p : R[X]) =
      Polynomial.taylor t (Polynomial.taylor s (p : R[X]))
    rw [Polynomial.taylor_taylor, add_comm]
  unfold stringExponential
  rw [h, LinearMap.toMatrix_mul, Matrix.transpose_mul]

@[simp] theorem stringExponential_zero (n : ℕ) : stringExponential n (0 : R) = 1 := by
  have h : (Polynomial.taylorLinearEquiv (0 : R) (n+1)).toLinearMap = 1 := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact Polynomial.taylor_zero _
  rw [stringExponential, h, LinearMap.toMatrix_one, Matrix.transpose_one]

theorem stringExponential_mul_neg (n : ℕ) (t : R) :
    stringExponential n t * stringExponential n (-t) = 1 := by
  rw [← stringExponential_add, add_neg_cancel, stringExponential_zero]

theorem stringExponential_neg_mul (n : ℕ) (t : R) :
    stringExponential n (-t) * stringExponential n t = 1 := by
  rw [← stringExponential_add, neg_add_cancel, stringExponential_zero]

theorem stringExponential_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (stringExponential n : R → Matrix (Fin (n+1)) (Fin (n+1)) R) := by
  intro s t h
  have h' := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) R =>
    A ⟨1, by omega⟩ ⟨0, by omega⟩) h
  simpa [stringExponential_entry] using h'

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley.Integral
variable {R : Type*} [CommRing R]

/-- Explicit integral-coefficient divided-power matrix over any ring. -/
def stringDividedMatrix (n k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i j => if i.val = j.val + k then (i.val.choose k : R) else 0

/-- The binomial action is precisely the finite divided-power exponential. -/
theorem stringExponential_eq_sum (n : ℕ) (t : R) :
    stringExponential n t =
      ∑ k ∈ Finset.range (n+1), t^k • (stringDividedMatrix n k : Matrix _ _ R) := by
  ext i j
  rw [stringExponential_entry]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hji : j.val ≤ i.val
  · rw [Finset.sum_eq_single_of_mem (i.val-j.val) (by simp; omega)]
    · simp [stringDividedMatrix, Nat.add_sub_of_le hji, Nat.choose_symm hji]
    · intro k hk hne
      have h : ¬i.val = j.val+k := by omega
      simp [stringDividedMatrix, h]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have h : ¬i.val = j.val+k := by omega
    simp [stringDividedMatrix, h]

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley.Integral

/-- The coefficient matrix is exactly that of the previously constructed
integral divided operator, in its original singleton basis. -/
theorem stringDividedMatrix_eq_toMatrix (n k : ℕ) :
    (stringDividedMatrix n k : Matrix _ _ ℤ) =
      LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
        (stringDividedPower n k) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change _ = stringDividedPower n k (Finsupp.single j 1) i
  rw [stringDividedPower_basis]
  by_cases h : i.val = j.val+k
  · have hlt : j.val+k < n+1 := by omega
    have hi : i = (⟨j.val+k, hlt⟩ : Fin (n+1)) := Fin.ext h
    simp [stringDividedMatrix, stringBasis, hlt, hi]
  · by_cases hlt : j.val+k < n+1
    · simp [stringDividedMatrix, stringBasis, hlt, h, Fin.ext_iff]
    · simp [stringDividedMatrix, stringBasis, hlt, h]

variable {R : Type*} [CommRing R]

/-- Coefficient reduction from the genuine integral divided powers. -/
theorem stringDividedMatrix_map (n k : ℕ) :
    (stringDividedMatrix n k : Matrix _ _ ℤ).map (Int.castRingHom R) =
      (stringDividedMatrix n k : Matrix _ _ R) := by
  ext i j
  simp [stringDividedMatrix]

/-- The actual invertible matrix, with its explicitly proved inverse. -/
noncomputable def stringRootElement (n : ℕ) (t : R) :
    (Matrix (Fin (n+1)) (Fin (n+1)) R)ˣ where
  val := stringExponential n t
  inv := stringExponential n (-t)
  val_inv := stringExponential_mul_neg n t
  inv_val := stringExponential_neg_mul n t

/-- The root parametrization is a homomorphism from the additive ring. -/
noncomputable def stringRootHom (n : ℕ) :
    Multiplicative R →* (Matrix (Fin (n+1)) (Fin (n+1)) R)ˣ where
  toFun t := stringRootElement n t.toAdd
  map_one' := Units.ext (stringExponential_zero n)
  map_mul' s t := Units.ext (stringExponential_add n s.toAdd t.toAdd)

theorem stringRootHom_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (stringRootHom (R := R) n) := by
  intro s t h
  have h' := congrArg Units.val h
  exact (stringExponential_injective n hn h' : s.toAdd = t.toAdd)

/-- The same matrix acting as an actual linear equivalence. -/
noncomputable def stringRootLinearEquiv (n : ℕ) (t : R) :
    (Fin (n+1) → R) ≃ₗ[R] (Fin (n+1) → R) :=
  Matrix.toLin'OfInv (stringExponential_neg_mul n t) (stringExponential_mul_neg n t)

end Atlas.Chevalley.Integral
