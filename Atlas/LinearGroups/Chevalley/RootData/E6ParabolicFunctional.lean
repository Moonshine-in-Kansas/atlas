import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The actual first-coordinate functional for the E6 minuscule parabolic.
This identifies a literal stabilizer inside the actual root-permutation Weyl
group. The D5 Weyl embedding and the 27-point minimum-length calculation are
separate obligations; neither is inferred from a Cartan diagram or orbit size. -/
noncomputable section
namespace Atlas.Chevalley.E6Parabolic
open Classical E6Data RootData

local instance : Fintype Root := Fintype.ofFinite Root

/-- Coordinate zero of the actual integral E6 root span, valued in the rationals. -/
def coordinateFunctional : pairing.rootSpan ℤ →+ ℚ where
  toFun x := (x.val 0 : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

/-- The five actual simple nodes other than the selected minuscule node zero. -/
def J : Finset base.support := Finset.univ.erase (baseIndexEquiv 0)

theorem coordinateFunctional_simple (i : Fin 6) :
    coordinateFunctional (pairing.rootSpanMem ℤ (baseIndexEquiv i).val) =
      if i = 0 then 1 else 0 := by
  change (((Pi.single (nodeEquiv.symm i) (1 : ℤ) : Fin 6 → ℤ) 0 : ℤ) : ℚ) = _
  fin_cases i <;> norm_num [nodeEquiv, Pi.single_apply] <;> decide

theorem coordinateFunctional_nonneg (i : base.support) :
    0 ≤ coordinateFunctional (pairing.rootSpanMem ℤ i.val) := by
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  rw [coordinateFunctional_simple]
  split_ifs <;> norm_num

theorem coordinateFunctional_zero_simple :
    rootFunctionalZeroSimple pairing base coordinateFunctional = J := by
  ext i
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ, true_and,
    coordinateFunctional_simple, J, Finset.mem_erase, and_true]
  simp only [baseIndexEquiv.injective.ne_iff]
  split_ifs <;> simp_all

/-- The actual functional stabilizer is the parabolic omitting node zero. -/
theorem coordinateFunctional_stabilizer :
    rootFunctionalStabilizer pairing coordinateFunctional =
      rootParabolicSubgroup pairing base J := by
  simpa only [coordinateFunctional_zero_simple] using
    rootFunctionalStabilizer_eq_parabolic pairing base coordinateFunctional
      coordinateFunctional_nonneg

/-- Membership is exactly preservation of coordinate zero on every actual root. -/
theorem mem_parabolic_iff_preserves_first (w : pairing.weylGroupToPerm.range) :
    w ∈ rootParabolicSubgroup pairing base J ↔
      ∀ β : Root, (w.val β).val 0 = β.val 0 := by
  rw [← coordinateFunctional_stabilizer]
  change (∀ β : Root, ((w.val β).val 0 : ℚ) = (β.val 0 : ℚ)) ↔ _
  constructor
  · intro h β
    exact Int.cast_injective (h β)
  · intro h β
    exact congrArg (fun z : ℤ => (z : ℚ)) (h β)

end Atlas.Chevalley.E6Parabolic
