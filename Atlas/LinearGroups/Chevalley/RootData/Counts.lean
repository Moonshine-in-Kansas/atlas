import Atlas.LinearGroups.Chevalley.Models
import Mathlib.Algebra.Ring.Parity

/-! Uniform actual-root counts. This connects the arithmetic
positive-root-number specification to the constructed total root sets. It does
not count positive subsets or finite groups. -/
namespace Atlas.Chevalley

/-- Total number of actual roots in all nine constructed coordinate families. -/
theorem rootDatum_root_card (Φ : RootType) :
    Nat.card (rootDatum Φ).Root = 2 * Φ.positiveRootNumber := by
  cases Φ with
  | A r hr =>
    change Nat.card (TypeAData.Root (r + 1)) = 2 * (r * (r + 1) / 2)
    rw [Nat.card_eq_fintype_card, TypeAData.card_root, Nat.add_sub_cancel]
    calc
      (r + 1) * r = r * (r + 1) := Nat.mul_comm _ _
      _ = (r * (r + 1) / 2) * 2 := (Nat.div_mul_cancel (Nat.two_dvd_mul_add_one r)).symm
      _ = 2 * (r * (r + 1) / 2) := Nat.mul_comm _ _
  | B r hr =>
    change Nat.card (ClassicalData.BRoot (r - 1 + 1)) = 2 * r ^ 2
    rw [Nat.card_eq_fintype_card, ClassicalData.card_broot, show r - 1 + 1 = r by omega]
  | C r hr =>
    change Nat.card (ClassicalData.BRoot (r - 1 + 1)) = 2 * r ^ 2
    rw [Nat.card_eq_fintype_card, ClassicalData.card_broot, show r - 1 + 1 = r by omega]
  | D r hr =>
    change Nat.card (ClassicalData.DRoot (r - 2 + 2)) = 2 * (r * (r - 1))
    rw [Nat.card_eq_fintype_card, ClassicalData.card_droot, show r - 2 + 2 = r by omega]
    exact Nat.mul_assoc _ _ _
  | E6 => exact Atlas.Comparisons.E6Lattice.card_roots
  | E7 => exact E7Data.root_card
  | E8 => exact E8Data.root_card
  | F4 => exact F4Data.root_card
  | G2 => exact G2Data.root_card

/-- The count also holds for the actual embedded root set, without duplicate labels. -/
theorem rootDatum_root_image_card (Φ : RootType) :
    Nat.card (Set.range (rootDatum Φ).pairing.root) = 2 * Φ.positiveRootNumber := by
  calc
    Nat.card (Set.range (rootDatum Φ).pairing.root) = Nat.card (rootDatum Φ).Root :=
      Nat.card_congr (Equiv.ofInjective (rootDatum Φ).pairing.root
        (rootDatum Φ).pairing.root.injective).symm
    _ = 2 * Φ.positiveRootNumber := rootDatum_root_card Φ

/-- Cardinality of the actual Cartan-plus-root basis used by the adjoint model. -/
theorem rootDatum_adjoint_basis_card (Φ : RootType) :
    Nat.card ((rootDatum Φ).base.support ⊕ (rootDatum Φ).Root) =
      Φ.rank + 2 * Φ.positiveRootNumber := by
  rw [Nat.card_sum, model_base_card, rootDatum_root_card]

end Atlas.Chevalley
