import Atlas.LinearGroups.Unitary.Determinant
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Norm-one scalar parameters in special unitary dimension n

This counts the actual scalar parameter group. Identifying its image with the
full special unitary center remains a separate structural obligation.
-/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Norm-one scalars whose n-th power is one. -/
def scalarParameters (n : ℕ) : Subgroup (normOne F K) := (powMonoidHom n).ker

theorem card_scalarParameters (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (scalarParameters F K n) = Nat.gcd n (Nat.card F + 1) := by
  rw [scalarParameters, IsCyclic.card_powMonoidHom_ker, normOne_card hdeg, Nat.gcd_comm]

/-- An actual scalar parameter gives a matrix in the retained SU carrier. -/
def scalarSpecial (hdeg : Module.finrank F K = 2) {n : ℕ}
    (a : scalarParameters F K n) : SU F K n hdeg :=
  ⟨(diagonalUnitary hdeg (fun _ => a.val)).val,
    (diagonalUnitary hdeg (fun _ => a.val)).prop, by
      change (Matrix.diagonal (fun _ : Fin n => ((a.val.val : Kˣ) : K))).det = 1
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have ha : a.val ^ n = 1 := a.prop
      exact congrArg (fun t : normOne F K => (t.val : K)) ha⟩

/-- Positive dimension ensures that the scalar parameter is retained faithfully. -/
theorem scalarSpecial_injective (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 0 < n) :
    Function.Injective (scalarSpecial F K hdeg (n := n)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (fun g : SU F K n hdeg => g.val ⟨0, hn⟩ ⟨0, hn⟩) hab
  exact h
end Atlas.Unitary
