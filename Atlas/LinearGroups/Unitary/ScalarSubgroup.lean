import Atlas.LinearGroups.Unitary.ScalarParameters
import Mathlib.GroupTheory.Coset.Card

/-! # The actual scalar subgroup inside the special unitary center

This constructs the scalar inclusion and counts its image. Equality with the
full center is deliberately a separate structural theorem.
-/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Multiplication of norm-one scalar parameters is actual matrix multiplication. -/
def scalarSpecialHom (hdeg : Module.finrank F K = 2) (n : ℕ) :
    scalarParameters F K n →* SU F K n hdeg where
  toFun := scalarSpecial F K hdeg
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (fun _ : Fin n => (1 : K)) = 1
    exact Matrix.diagonal_one
  map_mul' a b := by
    apply Subtype.ext
    change Matrix.diagonal (fun _ : Fin n => (((a * b).val.val : Kˣ) : K)) =
      Matrix.diagonal (fun _ : Fin n => ((a.val.val : Kˣ) : K)) *
      Matrix.diagonal (fun _ : Fin n => ((b.val.val : Kˣ) : K))
    rw [Matrix.diagonal_mul_diagonal]
    rfl

theorem scalarSpecial_mem_center (hdeg : Module.finrank F K = 2) (n : ℕ)
    (a : scalarParameters F K n) :
    scalarSpecial F K hdeg a ∈ Subgroup.center (SU F K n hdeg) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change g.val * Matrix.diagonal (fun _ : Fin n => ((a.val.val : Kˣ) : K)) =
    Matrix.diagonal (fun _ : Fin n => ((a.val.val : Kˣ) : K)) * g.val
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

/-- The scalar homomorphism with codomain the actual group-theoretic center. -/
def scalarCenterHom (hdeg : Module.finrank F K = 2) (n : ℕ) :
    scalarParameters F K n →* Subgroup.center (SU F K n hdeg) :=
  (scalarSpecialHom F K hdeg n).codRestrict _ (scalarSpecial_mem_center F K hdeg n)

theorem scalarCenterHom_injective (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 0 < n) :
    Function.Injective (scalarCenterHom F K hdeg n) := by
  intro a b hab
  exact scalarSpecial_injective F K hdeg hn (congrArg Subtype.val hab)

/-- The counted scalar subgroup, as a subgroup of the retained SU carrier. -/
def scalarSubgroup (hdeg : Module.finrank F K = 2) (n : ℕ) : Subgroup (SU F K n hdeg) :=
  (scalarSpecialHom F K hdeg n).range

theorem scalarSubgroup_le_center (hdeg : Module.finrank F K = 2) (n : ℕ) :
    scalarSubgroup F K hdeg n ≤ Subgroup.center (SU F K n hdeg) := by
  rintro _ ⟨a, rfl⟩
  exact scalarSpecial_mem_center F K hdeg n a

theorem card_scalarSubgroup (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 0 < n) :
    Nat.card (scalarSubgroup F K hdeg n) = Nat.gcd n (Nat.card F + 1) := by
  rw [scalarSubgroup, ← Nat.card_congr
    (MonoidHom.ofInjective (f := scalarSpecialHom F K hdeg n)
      (scalarSpecial_injective F K hdeg hn)).toEquiv]
  exact card_scalarParameters F K hdeg n

/-- The scalar order necessarily divides the full center order. -/
theorem scalar_order_dvd_center (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 0 < n) :
    Nat.gcd n (Nat.card F + 1) ∣ Nat.card (Subgroup.center (SU F K n hdeg)) := by
  rw [← card_scalarParameters F K hdeg n]
  exact Subgroup.card_dvd_of_injective (scalarCenterHom F K hdeg n)
    (scalarCenterHom_injective F K hdeg hn)

theorem scalar_order_le_center (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 0 < n) :
    Nat.gcd n (Nat.card F + 1) ≤ Nat.card (Subgroup.center (SU F K n hdeg)) := by
  rw [← card_scalarParameters F K hdeg n]
  exact Nat.card_le_card_of_injective (scalarCenterHom F K hdeg n)
    (scalarCenterHom_injective F K hdeg hn)

end Atlas.Unitary
