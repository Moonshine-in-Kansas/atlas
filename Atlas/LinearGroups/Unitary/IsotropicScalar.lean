import Atlas.LinearGroups.Unitary.Hermitian
import Atlas.FieldTheory.FiniteQuadraticFibers
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree

/-! # Preservation of isotropic lines forces a scalar matrix

The argument uses the q+1 isotropic lines in each coordinate plane, through a
quadratic polynomial identity. No group order, generation or simplicity is used.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix Polynomial Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- A quadratic polynomial vanishing on a nonzero norm fibre is zero. -/
theorem quadratic_eq_zero_on_norm_fiber (hdeg : Module.finrank F K = 2)
    (b : F) (hb : b ≠ 0) (p : K[X]) (hp : p.natDegree ≤ 2)
    (hz : ∀ a : K, norm F K a = b → p.eval a = 0) : p = 0 := by
  classical
  letI := Fintype.ofFinite {a : K // norm F K a = b}
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun a : {a : K // norm F K a = b} => a.val) Subtype.val_injective
    (fun a => hz a.val a.prop)
  have hc := norm_fiber_card (K := K) hdeg b hb
  rw [Nat.card_eq_fintype_card] at hc
  have hq := Finite.one_lt_card (α := F)
  omega

/-- Every matrix preserving each isotropic line is scalar, even over GF(4). -/
theorem matrix_scalar_of_isotropic_lines (hdeg : Module.finrank F K = 2)
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) K)
    (hlines : ∀ v : Fin n → K, v ≠ 0 → hermitian F K v v = 0 →
      ∃ c : K, A *ᵥ v = c • v) :
    ∃ c : K, A = Matrix.diagonal (fun _ => c) := by
  classical
  have hpair (i j : Fin n) (hij : i ≠ j) : A i j = 0 ∧ A i i = A j j := by
    let p : K[X] := C (A i j) * X ^ 2 + C (A i i - A j j) * X - C (A j i)
    have hp : p = 0 := by
      apply quadratic_eq_zero_on_norm_fiber hdeg (-1 : F) (neg_ne_zero.mpr one_ne_zero) p
      · dsimp [p]
        compute_degree
      · intro a ha
        let v : Fin n → K := Pi.single i 1 + a • Pi.single j 1
        have hvi : v i = 1 := by simp [v, hij, Ne.symm hij]
        have hv : v ≠ 0 := by
          intro he
          have := congrFun he i
          simpa [hvi] using this
        have hnorm : a * conjugation F K a = -1 := by
          rw [← norm_formula hdeg, ha, map_neg, map_one]
        have hiso : hermitian F K v v = 0 := by
          simp [v, hermitian_add_left, hermitian_add_right, hermitian_smul_left,
            hermitian_smul_right, hermitian_single_right, hij, Ne.symm hij, mul_comm,
            hnorm]
        obtain ⟨c, hc⟩ := hlines v hv hiso
        have hi := congrFun hc i
        have hj := congrFun hc j
        simp only [v, mulVec_add, mulVec_smul, mulVec_single_one, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul] at hi hj
        simp [Pi.single_apply, hij, Ne.symm hij] at hi hj
        simp only [p, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]
        linear_combination a * hi - hj
    constructor
    · have he := congrArg (fun f : K[X] => f.coeff 2) hp
      simpa [p] using he
    · have he := congrArg (fun f : K[X] => f.coeff 1) hp
      have : A i i - A j j = 0 := by simpa [p] using he
      exact sub_eq_zero.mp this
  let k : Fin n := ⟨0, hn⟩
  refine ⟨A k k, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    by_cases hik : i = k
    · simp [hik]
    · exact (hpair i k hik).2
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact (hpair i j hij).1
end Atlas.Unitary
