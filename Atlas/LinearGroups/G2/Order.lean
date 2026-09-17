import Atlas.LinearGroups.G2.PointStabilizer
import Atlas.LinearGroups.SL2Order
import Mathlib.GroupTheory.GroupAction.Quotient

namespace Atlas.G2
variable {K : Type*} [Field K] [Finite K]

/-- Exact orbit–stabilizer count for the full octonion automorphism model. -/
theorem card_Model_eq_points_mul_stabilizer : Nat.card (Model K) =
    Nat.card (SingularPoints K) * Nat.card (pointStabilizer (K := K)) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Model K)
    (firstPoint (K := K))),Nat.card_prod]
  congr 1
  rw [MulAction.orbit_eq_univ]
  exact Nat.card_congr (Equiv.Set.univ (SingularPoints K))

/-- The exact uniform order of the actual split-octonion automorphism group. -/
theorem card_Model : Nat.card (Model K) =
    Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
  have hc := Nat.card_congr (nonzeroSingularEquivPointsUnits K)
  rw [card_nonzeroSingularOctonions,Nat.card_prod,Nat.card_units] at hc
  rw [card_Model_eq_points_mul_stabilizer,card_pointStabilizer,Atlas.card_sl_two]
  calc
    _ = (Nat.card (SingularPoints K) * (Nat.card K - 1)) *
        Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) := by ring
    _ = _ := by rw [← hc]; ring

theorem card_fixingFirstVector_formula : Nat.card (fixingFirstVector (K := K)) =
    Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) := by
  rw [card_fixingFirstVector_SL2,Atlas.card_sl_two]
  ring

theorem card_pointStabilizer_formula : Nat.card (pointStabilizer (K := K)) =
    Nat.card K ^ 6 * (Nat.card K - 1)^2 * (Nat.card K + 1) := by
  let q := Nat.card K
  have hq : 1 < q := Finite.one_lt_card (α := K)
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hs := Nat.sub_add_cancel (show 1 ≤ q by omega)
  have hs2 := Nat.sub_add_cancel hq2
  have he : q^2-1 = (q-1)*(q+1) := by nlinarith
  rw [card_pointStabilizer,Atlas.card_sl_two]
  change (q-1)*(q^5*(q*(q^2-1))) = q^6*(q-1)^2*(q+1)
  rw [he]
  ring
end Atlas.G2
