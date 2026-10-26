import Atlas.LinearGroups.Chevalley.RootData.E7
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer

/-! The actual E7 dominant coordinate functional and its exact zero-wall
parabolic stabilizer. No E6 identification or parabolic order is assumed. -/
noncomputable section
set_option maxRecDepth 32768
namespace Atlas.Chevalley.E7WeightOrbit
open Classical RootData E7Data

def functional : pairing.rootSpan ℤ →+ ℚ where
  toFun x := (x.val 6 : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

/-- The pinned first six nodes, omitting the minuscule node6. -/
def J : Finset base.support := Finset.univ.erase (baseIndexEquiv 6)

theorem functional_simple (i : Fin 7) :
    functional (pairing.rootSpanMem ℤ (baseIndexEquiv i).val) =
      if i = 6 then 1 else 0 := by
  change ((datum.root (datum.simpleIndex i)) 6 : ℚ) = _
  rw [datum.simple_coordinates]
  simp [Pi.single_apply, eq_comm]

theorem functional_nonneg (i : base.support) :
    0 ≤ functional (pairing.rootSpanMem ℤ i.val) := by
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  rw [functional_simple]
  split_ifs <;> norm_num

theorem functional_zero_simple : rootFunctionalZeroSimple pairing base functional = J := by
  ext i
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ, true_and,
    functional_simple, J, Finset.mem_erase, and_true]
  by_cases hk : k = 6
  · subst k
    simp
  · have hne : baseIndexEquiv k ≠ baseIndexEquiv 6 :=
      fun he => hk (baseIndexEquiv.injective he)
    simp [hk, hne]

theorem functional_stabilizer : rootFunctionalStabilizer pairing functional =
    rootParabolicSubgroup pairing base J := by
  simpa only [functional_zero_simple] using
    rootFunctionalStabilizer_eq_parabolic pairing base functional functional_nonneg

/-- The stabilizer is an actual subgroup of the root-permutation Weyl image. -/
theorem mem_parabolic_iff_preserves_coordinate (w : pairing.weylGroupToPerm.range) :
    w ∈ rootParabolicSubgroup pairing base J ↔
      ∀ β : E7Data.Root, E7Table.coordinates (w.val β) 6 = E7Table.coordinates β 6 := by
  rw [← functional_stabilizer]
  change (∀ β : E7Data.Root,
    (E7Table.coordinates (w.val β) 6 : ℚ) = (E7Table.coordinates β 6 : ℚ)) ↔ _
  constructor
  · intro h β
    exact Int.cast_injective (h β)
  · intro h β
    exact congrArg (fun z : ℤ => (z : ℚ)) (h β)

end Atlas.Chevalley.E7WeightOrbit
