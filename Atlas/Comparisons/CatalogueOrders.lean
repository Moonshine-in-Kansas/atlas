import Atlas.OrderArithmetic.Orders
import Atlas.Families.Cyclic.Basic
import Atlas.Families.Alternating.Basic
import Atlas.LinearGroups.ProjectiveSpecialLinear
import Atlas.LinearGroups.Unitary.ProjectiveOrder
import Atlas.LinearGroups.Symplectic.ProjectiveOrder
import Atlas.LinearGroups.Orthogonal.BAllRanks
import Atlas.LinearGroups.Orthogonal.DFamily
import Atlas.LinearGroups.Orthogonal.Minus.Family
import Atlas.LinearGroups.F4.Order
import Atlas.LinearGroups.G2.Order
import Atlas.LinearGroups.Triality.Order
import Atlas.LinearGroups.SuzukiFamily.Order
import Atlas.LinearGroups.ReeG2.Order
import Atlas.Tits.Order
import Atlas.Sporadic.Mathieu11
import Atlas.Sporadic.Mathieu12
import Atlas.Sporadic.Mathieu22
import Atlas.Sporadic.Mathieu23
import Atlas.Sporadic.Mathieu24Construction
import Atlas.Sporadic.Conway1
import Atlas.Sporadic.Conway2
import Atlas.Sporadic.Conway3
import Atlas.Sporadic.McLaughlin
import Atlas.Sporadic.HigmanSims
import Atlas.Sporadic.Suzuki
import Atlas.Sporadic.Janko2
import Atlas.Sporadic.Fischer22
import Atlas.Sporadic.Fischer23
import Atlas.Sporadic.Fischer24Prime
import Atlas.Sporadic.Rudvalis

/-! Bridges from existing ATLAS carriers to the independent numerical specification.
No group is defined or identified by its order in this file. -/
namespace Atlas.Comparisons.CatalogueOrders
open scoped BigOperators
open Atlas.OrderArithmetic

theorem Tits_card : Nat.card Atlas.Tits.Model =
    order (.fixed .Tits) := by
  rw [Atlas.Tits.card]
  norm_num [order, fixedOrder]

theorem M11_card (D : Atlas.Codes.Dodecad) (a : Atlas.Codes.Mathieu12Points D) : Nat.card (Atlas.Sporadic.Mathieu11.Model D a) =
    order (.fixed .M11) := by
  rw [Atlas.Sporadic.Mathieu11.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Mathieu11.order]

theorem M12_card (D : Atlas.Codes.Dodecad) : Nat.card (Atlas.Sporadic.Mathieu12.Model D) =
    order (.fixed .M12) := by
  rw [Atlas.Sporadic.Mathieu12.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Mathieu12.order]

theorem M22_card (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) : Nat.card (Atlas.Sporadic.Mathieu22.Model a b) =
    order (.fixed .M22) := by
  rw [Atlas.Sporadic.Mathieu22.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Mathieu22.order]

theorem M23_card (a : Atlas.Codes.Omega) : Nat.card (Atlas.Sporadic.Mathieu23.Model a) =
    order (.fixed .M23) := by
  rw [Atlas.Sporadic.Mathieu23.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Mathieu23.order]

theorem M24_card : Nat.card Atlas.Sporadic.Mathieu24.Model =
    order (.fixed .M24) := by
  rw [Atlas.Sporadic.Mathieu24.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Mathieu24.expectedOrder]

theorem Co1_card : Nat.card Atlas.Sporadic.Conway1.Model =
    order (.fixed .Co1) := by
  rw [Atlas.Sporadic.Conway1.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Conway1.order]

theorem Co2_card : Nat.card Atlas.Sporadic.Conway2.Model =
    order (.fixed .Co2) := by
  rw [Atlas.Sporadic.Conway2.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Conway2.order]

theorem Co3_card : Nat.card Atlas.Sporadic.Conway3.Model =
    order (.fixed .Co3) := by
  rw [Atlas.Sporadic.Conway3.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.Conway3.order]

theorem McL_card : Nat.card Atlas.Sporadic.McLaughlin.Model =
    order (.fixed .McL) := by
  rw [Atlas.Sporadic.McLaughlin.card]
  norm_num [order, fixedOrder, Atlas.Sporadic.McLaughlin.order]

theorem HS_card : Nat.card Atlas.Sporadic.HigmanSims.Model =
    order (.fixed .HS) := by
  rw [Atlas.Sporadic.HigmanSims.card]
  norm_num [order, fixedOrder]

theorem Suz_card : Nat.card Atlas.Sporadic.Suzuki.Model =
    order (.fixed .Suz) := by
  rw [Atlas.Sporadic.Suzuki.card]
  norm_num [order, fixedOrder]

theorem J2_card : Nat.card Atlas.Sporadic.Janko2.Model =
    order (.fixed .J2) := by
  rw [Atlas.Sporadic.Janko2.card]
  norm_num [order, fixedOrder]

theorem Fi22_card : Nat.card Atlas.Sporadic.Fischer22.Model =
    order (.fixed .Fi22) := by
  rw [Atlas.Sporadic.Fischer22.card]
  norm_num [order, fixedOrder]

theorem Fi23_card : Nat.card Atlas.Sporadic.Fischer23.Model =
    order (.fixed .Fi23) := by
  rw [Atlas.Sporadic.Fischer23.card]
  norm_num [order, fixedOrder]

theorem Fi24prime_card : Nat.card Atlas.Sporadic.Fischer24Prime.Model =
    order (.fixed .Fi24prime) := by
  rw [Atlas.Sporadic.Fischer24Prime.card]
  norm_num [order, fixedOrder]

theorem Ru_card : Nat.card Atlas.Sporadic.Rudvalis.Model =
    order (.fixed .Ru) := by
  rw [Atlas.Sporadic.Rudvalis.card]
  norm_num [order, fixedOrder]

theorem cyclic_card (p : ℕ) (hp : 0 < p) :
    Nat.card (Atlas.Families.Cyclic.Model p) = order (.cyclic p) :=
  Atlas.Families.Cyclic.card p hp

theorem alternating_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Atlas.Families.Alternating.Model n) = order (.alternating n) :=
  Atlas.Families.Alternating.card_factorial n hn

theorem field_card_primePower (F : Type*) [Field F] [Finite F] :
    PrimePower (Nat.card F) := by
  letI := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hn⟩ := FiniteField.card' F
  exact ⟨p, n, hp, n.pos, (Nat.card_eq_fintype_card).trans hn⟩

theorem linear_card (F : Type*) [Field F] [Finite F] (d : ℕ) [NeZero d] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin d) F) =
      order (.linear d (Nat.card F)) :=
  Atlas.card_psl_factor d

theorem unitary_card (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (d : ℕ) (hd : 0 < d) :
    Nat.card (Atlas.Unitary.PSU F K d hdeg) = order (.unitary d (Nat.card F)) :=
  Atlas.Unitary.card_psu_factor hdeg d hd

private theorem shifted_product (q n : ℕ) :
    (∏ i ∈ Finset.range n, (q ^ (2 * (i + 1)) - 1)) =
      ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [Nat.add_comm]

theorem symplectic_card (F : Type*) [Field F] [Finite F] (r : ℕ) (hr : 0 < r) :
    Nat.card (Atlas.Symplectic.PSp r F) = order (.C r (Nat.card F)) := by
  rw [Atlas.Symplectic.card_psp hr]
  simp only [Atlas.Symplectic.orderNumerator, order, numerator, fieldSize,
    characteristicExponent, OrderArithmetic.residual, denominator, pow_two, shifted_product]

theorem B_card (F : Type*) [Field F] [Finite F] (r : ℕ) (hr : 1 ≤ r) :
    Nat.card (Atlas.Orthogonal.B r F) = order (.B r (Nat.card F)) := by
  rw [Atlas.Orthogonal.B_card_all_rank r hr]
  simp only [Atlas.Orthogonal.B_order, Atlas.Orthogonal.B_order_numerator,
    Atlas.Orthogonal.B_order_denominator, order, numerator, fieldSize,
    characteristicExponent, OrderArithmetic.residual, denominator, pow_two, shifted_product]

theorem Dplus_card (F : Type*) [Field F] [Finite F] (r : ℕ) (hr : 4 ≤ r) :
    Nat.card (Atlas.Orthogonal.DPlus r F) = order (.Dplus r (Nat.card F)) := by
  rw [Atlas.Orthogonal.DPlus_card r hr]
  simp only [Atlas.Orthogonal.DPlus_order, Atlas.Orthogonal.DPlus_order_numerator,
    Atlas.Orthogonal.DPlus_order_denominator, order, numerator, fieldSize,
    characteristicExponent, OrderArithmetic.residual, denominator, shifted_product, mul_assoc]

theorem Dminus_card (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (r : ℕ) (hr : 3 ≤ r) :
    Nat.card (Atlas.Orthogonal.DMinus r F K hdeg) = order (.Dminus r (Nat.card F)) := by
  rw [Atlas.Orthogonal.Minus.family_order hdeg r hr]
  simp only [Atlas.Orthogonal.Minus.orderNumerator, order, numerator, fieldSize,
    characteristicExponent, OrderArithmetic.residual, denominator, shifted_product, mul_assoc]

theorem G2_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Atlas.G2.Model F) = order (.G2 (Nat.card F)) := by
  simpa [order, numerator, fieldSize, characteristicExponent, OrderArithmetic.residual, denominator,
    mul_assoc] using Atlas.G2.card_Model (K := F)

theorem F4_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Atlas.F4.Model F) = order (.F4 (Nat.card F)) := by
  rw [Atlas.F4.card_Model]
  norm_num [order, numerator, fieldSize, characteristicExponent, OrderArithmetic.residual, denominator]
  ring

theorem triality_card (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 3) :
    Nat.card (Atlas.Triality.Group F K) = order (.trialityD4 (Nat.card F)) := by
  simpa [order, numerator, fieldSize, characteristicExponent, OrderArithmetic.residual, denominator,
    mul_assoc] using Atlas.Triality.card_group F K hdeg

theorem suzuki_card (F : Type*) [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (Atlas.SuzukiFamily.Group F m) = order (.suzuki (Nat.card F)) := by
  simpa [order, numerator, fieldSize, characteristicExponent, OrderArithmetic.residual, denominator,
    mul_assoc] using Atlas.SuzukiFamily.card_group m hcard

theorem smallRee_card (F : Type*) [Field F] [Finite F] [CharP F 3]
    (m : ℕ) (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    Nat.card (Atlas.ReeG2.Model F m) = order (.smallRee (Nat.card F)) := by
  simpa [order, numerator, fieldSize, characteristicExponent, OrderArithmetic.residual, denominator,
    mul_assoc] using Atlas.ReeG2.order m hcard

end Atlas.Comparisons.CatalogueOrders
