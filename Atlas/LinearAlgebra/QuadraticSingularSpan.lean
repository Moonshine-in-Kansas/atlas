import Atlas.LinearAlgebra.QuadraticSplit

/-! # Singular vectors span every quadratic space containing a hyperbolic plane -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
  (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
/-- A perpendicular vector is the sum of three singular vectors. -/
theorem complement_singular_decomposition (w : complement Q e f) :
    Q (w.val + e - Q w.val • f) = 0 := by
  have hwe : Q.polarBilin w.val e = 0 := w.prop.1
  have hwf : Q.polarBilin w.val f = 0 := w.prop.2
  have hqe : Q (w.val + e) = Q w.val := by
    rw [QuadraticMap.map_add Q]
    change Q w.val + Q e + Q.polarBilin w.val e = Q w.val
    rw [he, hwe, add_zero, add_zero]
  rw [sub_eq_add_neg, ← neg_smul, add_smul, hqe]
  simp only [he, hf, hwe, map_add, LinearMap.add_apply, hwf, hef, mul_zero, add_zero]
  ring

include e f he hf hef in
/-- A linear functional vanishing on singular vectors vanishes everywhere. -/
theorem linear_zero_of_singular (l : V →ₗ[F] F)
    (hl : ∀ x, Q x = 0 → l x = 0) : l = 0 := by
  have hlw : ∀ w : complement Q e f, l w.val = 0 := by
    intro w
    have h := hl _ (complement_singular_decomposition Q e f he hf hef w)
    rw [map_sub, map_add, map_smul, hl e he, hl f hf, smul_zero, add_zero, sub_zero] at h
    exact h
  apply LinearMap.ext
  intro x
  let t := split Q e f he hf hef x
  have hx : x = t.1.1 • e + t.1.2 • f + t.2.val :=
    ((split Q e f he hf hef).symm_apply_apply x).symm
  rw [hx, map_add, map_add, map_smul, map_smul, hl e he, hl f hf, hlw,
    smul_zero, smul_zero, zero_add, add_zero]
  rfl

include e f he hf hef in
/-- A nonzero linear functional has a singular witness. -/
theorem exists_singular_functional_ne_zero (l : V →ₗ[F] F) (hl : l ≠ 0) :
    ∃ x, Q x = 0 ∧ l x ≠ 0 := by
  classical
  by_contra! h
  exact hl (linear_zero_of_singular Q e f he hf hef l h)

end Atlas.Quadratic
