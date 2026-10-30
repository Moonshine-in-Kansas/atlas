import Atlas.LinearGroups.Chevalley.TwistedE6.CompanionDiagram
import Atlas.LinearGroups.Chevalley.TwistedE6.AdjointTwist

/-! The actual graph--Frobenius equalizer in the selected simply connected
E6 model, with its equivariant adjoint projection. Fixed-point surjectivity
and the full center are separate theorems, not part of this definition. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open E6Data Atlas.GroupTheory
local instance companionTwistRootFintype : Fintype Root := Fintype.ofFinite Root
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

abbrev companionFrobenius : SelectedWeightCompanion .E6 K ≃* SelectedWeightCompanion .E6 K :=
  weightCompanionFrobenius (rootDatum .E6).pairing (rootDatum .E6).base F K
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6)

theorem companionDiagram_commute_frobenius :
    Function.Commute (companionDiagram K) (companionFrobenius F K) := by
  intro g
  exact (companionDiagram_map (Atlas.FiniteQuadratic.conjugation F K).toRingHom g).symm

def companionTwist : SelectedWeightCompanion .E6 K ≃* SelectedWeightCompanion .E6 K :=
  graphFieldTwist (companionDiagram K) (companionFrobenius F K)

theorem companionTwist_involutive (hdeg : Module.finrank F K = 2) :
    Function.Involutive (companionTwist F K) :=
  graphFieldTwist_involutive _ _ (companionDiagram_involutive K)
    (weightCompanionFrobenius_involutive (rootDatum .E6).pairing (rootDatum .E6).base
      F K (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) hdeg)
    (companionDiagram_commute_frobenius F K)

@[simp] theorem companionTwist_X (i : Fin 6) (t : K) :
    companionTwist F K (selectedWeightCompanionX .E6 K i t) =
      selectedWeightCompanionX .E6 K (simpleNode i) (t ^ Nat.card F) := by
  change companionDiagram K (companionFrobenius F K (selectedWeightCompanionX .E6 K i t)) = _
  rw [show companionFrobenius F K (selectedWeightCompanionX .E6 K i t) =
      selectedWeightCompanionX .E6 K i (t ^ Nat.card F) from
    weightCompanionFrobenius_X (rootDatum .E6).pairing (rootDatum .E6).base F K
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) ((rootDatum .E6).indexEquiv i) t,
    companionDiagram_X]

@[simp] theorem companionTwist_Y (i : Fin 6) (t : K) :
    companionTwist F K (selectedWeightCompanionY .E6 K i t) =
      selectedWeightCompanionY .E6 K (simpleNode i) (t ^ Nat.card F) := by
  change companionDiagram K (companionFrobenius F K (selectedWeightCompanionY .E6 K i t)) = _
  rw [show companionFrobenius F K (selectedWeightCompanionY .E6 K i t) =
      selectedWeightCompanionY .E6 K i (t ^ Nat.card F) from
    weightCompanionFrobenius_Y (rootDatum .E6).pairing (rootDatum .E6).base F K
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) ((rootDatum .E6).indexEquiv i) t,
    companionDiagram_Y]

theorem companionTwist_rho (g : SelectedWeightCompanion .E6 K) :
    selectedWeightCompanionRho .E6 K (companionTwist F K g) =
      adjointTwist F K (selectedWeightCompanionRho .E6 K g) := by
  change selectedWeightCompanionRho .E6 K
    (companionDiagram K (companionFrobenius F K g)) = _
  rw [companionDiagram_rho]
  rfl

def companionFixedSubgroup : Subgroup (SelectedWeightCompanion .E6 K) :=
  automorphismFixedSubgroup (companionTwist F K)

theorem mem_companionFixedSubgroup_iff (g : SelectedWeightCompanion .E6 K) :
    g ∈ companionFixedSubgroup F K ↔ companionFrobenius F K g = companionDiagram K g :=
  mem_graphFieldFixed_iff _ _ (companionDiagram_involutive K) g

def companionFixedProjection : companionFixedSubgroup F K →* adjointFixedSubgroup F K :=
  fixedSubgroupMap (companionTwist F K) (adjointTwist F K)
    (selectedWeightCompanionRho .E6 K) (companionTwist_rho F K)

@[simp] theorem companionFixedProjection_val (g : companionFixedSubgroup F K) :
    (companionFixedProjection F K g).val = selectedWeightCompanionRho .E6 K g.val := rfl

end Atlas.Chevalley.TwistedE6
