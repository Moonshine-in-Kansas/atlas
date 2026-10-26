import Atlas.LinearGroups.Chevalley.RootData.ParabolicCosetDecomposition
import Atlas.LinearGroups.Chevalley.RootData.RootWeylPoincare
import Mathlib.Data.Fintype.BigOperators

/-! Multiplicative factorization of the actual Weyl-length sum by actual
parabolic coset coordinates. Neither factor is evaluated by a target formula. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (J : Finset b.support)
local instance : Fintype P.weylGroupToPerm.range := Fintype.ofFinite _
local instance : Fintype (rootParabolicRepresentatives P b J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup P b J) := Fintype.ofFinite _

theorem rootWeylPoincareEval_parabolic_factor (q : ℕ) :
    rootWeylPoincareEval P b q =
      (∑ x : rootParabolicRepresentatives P b J, q ^ rootWeylLength P b x.val) *
        (∑ v : rootParabolicSubgroup P b J, q ^ rootWeylLength P b v.val) := by
  change (∑ w : P.weylGroupToPerm.range, q ^ rootWeylLength P b w) = _
  calc
    _ = ∑ p : rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J,
        q ^ rootWeylLength P b (rootParabolicProductEquiv P b J p) :=
      ((rootParabolicProductEquiv P b J).sum_comp
        (fun w => q ^ rootWeylLength P b w)).symm
    _ = ∑ p : rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J,
        q ^ rootWeylLength P b p.1.val * q ^ rootWeylLength P b p.2.val := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [rootParabolicProductEquiv_length, pow_add]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

end Atlas.Chevalley.RootData
