import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinCenter
import Atlas.LinearGroups.Chevalley.Comparison.TypeBOrthogonalSurjective
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBCOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterCounts
import Atlas.LinearGroups.Orthogonal.BConstruction
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The kernel of the actual natural B map is the full source center, using
its proved surjectivity and independent finite orders. The binary rank-two
case is included; neither source nor target simplicity is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Atlas.Orthogonal
variable (n : ℕ) (hn : 2 ≤ n+1) (K : Type*) [Field K] [Finite K]

theorem companion_card_eq_elementary_mul_gcd :
    Nat.card (SelectedWeightCompanion (.B (n+1) hn) K) =
      Nat.card (elementarySubgroup (formB (n+1) K)) * Nat.gcd 2 (Nat.card K - 1) := by
  rw [selectedWeightCompanion_B_card]
  have h := B_card_mul_denominator (F := K) (n+1) hn
  rw [Nat.card_congr (B_elementaryEquiv (F := K) (n+1) hn).toEquiv] at h
  simpa only [B_order_denominator, B_order_numerator, pow_two] using h.symm

theorem elementaryHom_ker_card :
    Nat.card (elementaryHom n hn K).ker = Nat.gcd 2 (Nat.card K - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (elementaryHom n hn K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (elementaryHom n hn K) (elementaryHom_surjective n hn K)).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := elementarySubgroup (formB (n+1) K)))
    (h.symm.trans (companion_card_eq_elementary_mul_gcd n hn K))

/-- This is the vector-action kernel equality, derived from scalar-center
inclusion and equal finite cardinalities, valid also for B2 over F2. -/
theorem elementaryHom_ker_eq_center :
    (elementaryHom n hn K).ker =
      Subgroup.center (SelectedWeightCompanion (.B (n+1) hn) K) := by
  letI : Fintype K := Fintype.ofFinite K
  apply (Subgroup.eq_of_le_of_card_ge (center_le_elementaryHom_ker n hn K) ?_).symm
  rw [elementaryHom_ker_card, selectedWeightCompanion_B_center_card]
  simp only [Nat.card_eq_fintype_card]
  exact le_rfl

end Atlas.Chevalley.Comparison.TypeB
