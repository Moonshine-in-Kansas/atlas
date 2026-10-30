import Atlas.LinearGroups.ReeF4.OppositePairStabilizer
import Atlas.LinearGroups.ReeF4.RootSuzukiScalarElementary
import Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity
import Atlas.GroupTheory.TransitiveFullStabilizer

/-! Full-model generation from actual opposite-pair transitivity and its full
stabilizer. Neither full group order nor simplicity is an input. -/
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem elementarySubgroup_eq_top {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) : elementarySubgroup hcard=⊤ := by
  apply Atlas.GroupTheory.subgroup_eq_top_of_full_stabilizer
    (elementarySubgroup hcard) (baseSpecialOppositePair (F := F) m)
  · rw [←oppositePairStabilizer_eq_suzukiProduct hcard]
    exact modelSuzukiProductSubgroup_le_elementary hcard
  · intro g
    exact elementary_specialOppositePair_transitive hcard
      (baseSpecialOppositePair m) (g • baseSpecialOppositePair m)

theorem model_isPerfect {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (hm : 1 ≤ m) : Group.IsPerfect (Model F m) := by
  constructor
  apply top_unique
  rw [←elementarySubgroup_eq_top hcard]
  exact elementarySubgroup_le_commutator hcard hm

end Atlas.ReeF4
