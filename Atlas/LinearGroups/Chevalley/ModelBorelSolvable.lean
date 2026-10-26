import Atlas.LinearGroups.Chevalley.ModelFlagAction
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusSolvable

/-! The actual adjoint Borel is solvable, by the already proved solvability
of the actual companion Borel and the original adjoint projection.
This does not assert primitivity, quasiprimitivity or simplicity. -/
noncomputable section
namespace Atlas.Chevalley

theorem modelBorel_isSolvable (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Group.IsSolvable (modelBorel Φ K) := by
  let B := positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K
  letI : Group.IsSolvable B := positiveWitnessedTorusJoin_isSolvable
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ)
  let f := (selectedWeightCompanionRho Φ K).comp B.subtype
  have h : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hr : f.range = modelBorel Φ K := by
    change ((selectedWeightCompanionRho Φ K).comp B.subtype).range =
      B.map (selectedWeightCompanionRho Φ K)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact h

end Atlas.Chevalley
