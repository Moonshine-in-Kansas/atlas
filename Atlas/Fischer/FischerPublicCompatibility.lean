import Atlas.Fischer.FischerConstruction
import Atlas.Sporadic.Fischer24

namespace Atlas.Sporadic.Fischer24Prime

theorem isSimpleGroup : IsSimpleGroup Model := simple

theorem exists_mul_ne_mul : ∃ g h : Model, g * h ≠ h * g := by
  by_contra hn
  push_neg at hn
  exact noncommutative (isMulCommutative_iff.mpr hn)

end Atlas.Sporadic.Fischer24Prime

namespace Atlas.Sporadic.Fischer23

theorem isSimpleGroup : IsSimpleGroup Model := simple

theorem exists_mul_ne_mul : ∃ g h : Model, g * h ≠ h * g := by
  by_contra hn
  push_neg at hn
  exact noncommutative (isMulCommutative_iff.mpr hn)

end Atlas.Sporadic.Fischer23

namespace Atlas.Sporadic.Fischer22

theorem isSimpleGroup : IsSimpleGroup Model := simple

theorem exists_mul_ne_mul : ∃ g h : Model, g * h ≠ h * g := by
  by_contra hn
  push_neg at hn
  exact noncommutative (isMulCommutative_iff.mpr hn)

end Atlas.Sporadic.Fischer22

noncomputable section
namespace Atlas.Sporadic.Fischer24
open Atlas.Fischer

/-- The full ray group's primitive action, on its original points. -/
theorem primitive : MulAction.IsPreprimitive Model Points := rootGeneratedRayGroup_primitive

/-- The empty centralizer quotient is canonically isomorphic to the full ray group. -/
abbrev RankThreeModel := ResidueGroup ∅
abbrev RankThreePoints := ResiduePoint ∅
abbrev rankThreeGroupComparison := rootGeneratedEmptyResidueEquiv
abbrev rankThreePointComparison := displayedRayEmptyResidueEquiv
abbrev rankThreeActionComparison := displayedRayEmptyResidueMap

theorem rankThree_action_compatible (g : Model) (x : Points) :
    rankThreePointComparison (g • x) = rankThreeGroupComparison g • rankThreePointComparison x :=
  rankThreeActionComparison.map_smul' g x

/-- The full stabilizer has three orbits under the explicit compatible action comparison. -/
theorem rank_three (i : Atlas.Codes.Omega) :
    Nat.card (MulAction.orbitRel.Quotient
      (MulAction.stabilizer RankThreeModel (residueBasicPoint ∅ i (by simp))) RankThreePoints) = 3 :=
  residueGroup_rank_three ∅ (by simp) i (by simp)

theorem subdegrees (i : Atlas.Codes.Omega) (j : Fin 3) :
    Nat.card {x : RankThreePoints // residueSuborbitIndex ∅ i (by simp) x = j} =
      (![1, 31671, 275264] : Fin 3 → ℕ) j := by
  simpa [fischerRankThreeSubdegree] using residueSuborbit_card ∅ (by simp) i (by simp) j

end Atlas.Sporadic.Fischer24
