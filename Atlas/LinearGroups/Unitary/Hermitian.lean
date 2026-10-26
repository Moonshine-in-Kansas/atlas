import Atlas.LinearGroups.Unitary.Basic

/-! # The standard Hermitian form and its retained unitary matrix action -/
noncomputable section
namespace Atlas.Unitary
open Matrix
open Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Linear in the first variable, conjugate-linear in the second. -/
def hermitian {n : ℕ} (v w : Fin n → K) : K :=
  ∑ i, v i * conjugation F K (w i)

variable {F K} {n : ℕ}

theorem hermitian_add_left (v w z : Fin n → K) :
    hermitian F K (v + w) z = hermitian F K v z + hermitian F K w z := by
  simp [hermitian, add_mul, Finset.sum_add_distrib]

theorem hermitian_add_right (v w z : Fin n → K) :
    hermitian F K v (w + z) = hermitian F K v w + hermitian F K v z := by
  simp [hermitian, map_add, mul_add, Finset.sum_add_distrib]

theorem hermitian_smul_left (a : K) (v w : Fin n → K) :
    hermitian F K (a • v) w = a * hermitian F K v w := by
  simp [hermitian, mul_assoc, Finset.mul_sum]

theorem hermitian_smul_right (a : K) (v w : Fin n → K) :
    hermitian F K v (a • w) = conjugation F K a * hermitian F K v w := by
  simp [hermitian, map_mul, Finset.mul_sum, mul_left_comm]

theorem hermitian_symmetry (hdeg : Module.finrank F K = 2) (v w : Fin n → K) :
    conjugation F K (hermitian F K v w) = hermitian F K w v := by
  simp only [hermitian, map_sum, map_mul, conjugation_conjugation hdeg, mul_comm]

@[simp] theorem hermitian_zero_left (w : Fin n → K) : hermitian F K 0 w = 0 := by
  simp [hermitian]
@[simp] theorem hermitian_zero_right (v : Fin n → K) : hermitian F K v 0 = 0 := by
  simp [hermitian]

@[simp] theorem hermitian_single_right (v : Fin n → K) (i : Fin n) :
    hermitian F K v (Pi.single i 1) = v i := by
  classical
  simp [hermitian, Pi.single_apply]

theorem hermitian_nondegenerate (v : Fin n → K)
    (hv : ∀ w, hermitian F K v w = 0) : v = 0 := by
  ext i
  change v i = 0
  simpa only [hermitian_single_right] using hv (Pi.single i 1)

theorem hermitian_self_fixed (hdeg : Module.finrank F K = 2) (v : Fin n → K) :
    conjugation F K (hermitian F K v v) = hermitian F K v v :=
  hermitian_symmetry hdeg v v

theorem hermitian_self_in_base (hdeg : Module.finrank F K = 2) (v : Fin n → K) :
    ∃ a : F, algebraMap F K a = hermitian F K v v :=
  (conjugation_fixed_iff hdeg _).mp (hermitian_self_fixed hdeg v)

/-- The matrix carrier preserves the chosen first-variable-linear convention. -/
theorem u_preserves_hermitian (hdeg : Module.finrank F K = 2)
    (g : U F K n hdeg) (v w : Fin n → K) :
    hermitian F K ((g : Matrix (Fin n) (Fin n) K) *ᵥ v)
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) = hermitian F K v w := by
  let := conjugationStarRing F K hdeg
  change (g.val *ᵥ v) ⬝ᵥ star (g.val *ᵥ w) = v ⬝ᵥ star w
  rw [dotProduct_comm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  have hg : g.valᴴ * g.val = 1 := g.prop.1
  rw [hg, one_mulVec, dotProduct_comm]

/-- The special carrier has exactly the unitary condition and determinant one. -/
theorem su_mem_iff (hdeg : Module.finrank F K = 2) (g : Matrix (Fin n) (Fin n) K) :
    (let := conjugationStarRing F K hdeg
     g ∈ Matrix.specialUnitaryGroup (Fin n) K) ↔
    (let := conjugationStarRing F K hdeg
     g ∈ Matrix.unitaryGroup (Fin n) K) ∧ g.det = 1 := Iff.rfl

/-- The matrix equation and preservation of the actual form are equivalent. -/
theorem mem_u_iff_preserves_hermitian (hdeg : Module.finrank F K = 2)
    (g : Matrix (Fin n) (Fin n) K) :
    (letI := conjugationStarRing F K hdeg
     g ∈ Matrix.unitaryGroup (Fin n) K) ↔
    ∀ v w, hermitian F K (g *ᵥ v) (g *ᵥ w) = hermitian F K v w := by
  let := conjugationStarRing F K hdeg
  constructor
  · intro hg v w
    exact u_preserves_hermitian hdeg ⟨g, hg⟩ v w
  · intro hg
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext i j
    change (∑ k, conjugation F K (g k i) * g k j) = if i = j then 1 else 0
    have h := hg (Pi.single j 1) (Pi.single i 1)
    simpa [hermitian, Matrix.mulVec_single_one, Matrix.mul_apply,
      Matrix.star_apply, conjugationStarRing, hermitian_single_right,
      Pi.single_apply, eq_comm, mul_comm] using h
end Atlas.Unitary
