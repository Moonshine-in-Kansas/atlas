import Atlas.LinearGroups.Unitary.ShellAction
import Atlas.LinearGroups.Unitary.StandardStabilizer
import Atlas.LinearGroups.Unitary.OrderFormula
import Atlas.LinearGroups.Unitary.Determinant

/-! # Independent orders of the actual full and special unitary matrix groups

Count the actual norm-one orbit, identify its full stabilizer by restriction
and extension, then apply the proved determinant exact sequence. No generation,
perfectness, simplicity, or external group recognition enters the proof.
-/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem card_u_zero (hdeg : Module.finrank F K = 2) : Nat.card (U F K 0 hdeg) = 1 := by
  have : Subsingleton (U F K 0 hdeg) := inferInstance
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- Orbit–stabilizer for the actual norm-one shell. -/
theorem card_u_succ (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (U F K (n + 1) hdeg) =
      Nat.card F ^ n * orderFactor (Nat.card F) (n + 1) * Nat.card (U F K n hdeg) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (U F K (n + 1) hdeg)
    (coordinateUnit (F := F) (K := K) (0 : Fin (n + 1)))), Nat.card_prod,
    Nat.card_congr (normOneOrbitEquiv hdeg _),
    Nat.card_congr (firstStabilizerEquiv (n := n) hdeg).toEquiv,
    card_normOneVectors hdeg n]

/-- Uniform order of the retained full unitary matrix group, including dimension zero. -/
theorem card_u (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (U F K n hdeg) = orderU (Nat.card F) n := by
  induction n with
  | zero => rw [card_u_zero hdeg, orderU_zero]
  | succ n ih => rw [card_u_succ hdeg n, ih, orderU_succ]

/-- Uniform order of the retained determinant-one unitary group in positive dimension. -/
theorem card_su (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 0 < n) :
    Nat.card (SU F K n hdeg) = orderSU (Nat.card F) n := by
  have h := card_su_mul_normOne hdeg hn
  rw [card_u hdeg n, orderU_eq_mul_orderSU (Nat.card F) n hn] at h
  nlinarith
/-- Conventional factored full-unitary order, with dimension and base field explicit. -/
theorem card_u_factor (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (U F K n hdeg) = Nat.card F ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 n, orderFactor (Nat.card F) i := by
  rw [card_u hdeg n, orderU_formula_Icc]

/-- Conventional factored special-unitary order for the same retained carrier. -/
theorem card_su_factor (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 0 < n) :
    Nat.card (SU F K n hdeg) = Nat.card F ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, orderFactor (Nat.card F) i := by
  rw [card_su hdeg n hn, orderSU_formula_Icc]
end Atlas.Unitary

