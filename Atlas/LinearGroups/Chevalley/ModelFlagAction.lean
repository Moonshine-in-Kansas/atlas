import Atlas.GroupTheory.NormalCoreSurjection
import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalCore
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterQuotient

/-! The actual adjoint model acts faithfully on its Borel cosets. The Borel
is the image of the existing positive-root/torus subgroup under the original
adjoint projection. This does not assert quasiprimitivity or simplicity. -/
noncomputable section
namespace Atlas.Chevalley

def modelBorel (Φ : RootType) (K : Type*) [Field K] : Subgroup (Model Φ K) :=
  (positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K).map (selectedWeightCompanionRho Φ K)

abbrev ModelFlag (Φ : RootType) (K : Type*) [Field K] := Model Φ K ⧸ modelBorel Φ K

theorem modelBorel_normalCore_eq_bot (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    (modelBorel Φ K).normalCore = ⊥ := by
  let B := positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K
  have hcore : B.normalCore = (selectedWeightCompanionRho Φ K).ker :=
    (positiveWitnessedTorusJoin_normalCore_eq_center
      (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
      (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
      (rootDatum_simpleDiamondProducts Φ)).trans
        (selectedWeightCompanion_center_eq_rhoKernel Φ K)
  change (B.map (selectedWeightCompanionRho Φ K)).normalCore = ⊥
  rw [Atlas.GroupTheory.normalCore_map_of_surjective _
    (selectedWeightCompanionRho_surjective Φ K) B (hcore ▸ B.normalCore_le),
    hcore, Subgroup.map_ker_self]

theorem model_flagAction_injective (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Function.Injective (MulAction.toPermHom (Model Φ K) (ModelFlag Φ K)) := by
  apply (MulAction.toPermHom (Model Φ K) (ModelFlag Φ K)).ker_eq_bot_iff.mp
  exact (Subgroup.normalCore_eq_ker (modelBorel Φ K)).symm.trans
    (modelBorel_normalCore_eq_bot Φ K)

end Atlas.Chevalley
