import Atlas.LinearGroups.Chevalley.TwistedE6.DualCompanionDiagram
import Atlas.LinearGroups.Chevalley.WeightCompanionEquiv
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionAdjoinOrbit

/-! The graph automorphism of the existing selected E6 companion. It is
transported from the actual two-block action through the established faithful
block restriction. Neither a group order nor simplicity is a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Classical E6Data Integral.Minuscule
local instance companionDiagramRootFintype : Fintype Root := Fintype.ofFinite Root
variable (K : Type*) [Field K]

def dualCompanionEquiv : DualCompanion K ≃* SelectedWeightCompanion .E6 K := by
  exact weightCompanionFamilyRestrictionEquiv pairing base dualOrbits dualOrbits_closed
    dualOrbits_minuscule Option.some K (rootDatum_simpleDiamondProducts .E6)
    (selectedWeightSet_spans .E6)

@[simp] theorem dualCompanionEquiv_X (i : Fin 6) (t : K) :
    dualCompanionEquiv K (weightCompanionX pairing base dualOrbits
      dualOrbits_closed dualOrbits_minuscule K (baseIndexEquiv i) t) =
      selectedWeightCompanionX .E6 K i t := rfl

@[simp] theorem dualCompanionEquiv_Y (i : Fin 6) (t : K) :
    dualCompanionEquiv K (weightCompanionY pairing base dualOrbits
      dualOrbits_closed dualOrbits_minuscule K (baseIndexEquiv i) t) =
      selectedWeightCompanionY .E6 K i t := rfl

theorem dualCompanionEquiv_rho (g : DualCompanion K) :
    selectedWeightCompanionRho .E6 K (dualCompanionEquiv K g) =
      weightCompanionRho pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule K g := rfl

def companionDiagram : SelectedWeightCompanion .E6 K ≃* SelectedWeightCompanion .E6 K :=
  (dualCompanionEquiv K).symm.trans ((dualCompanionDiagram K).trans (dualCompanionEquiv K))

theorem companionDiagram_involutive : Function.Involutive (companionDiagram K) := by
  intro g
  simp only [companionDiagram, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [dualCompanionDiagram_involutive K ((dualCompanionEquiv K).symm g),
    MulEquiv.apply_symm_apply]

@[simp] theorem companionDiagram_X (i : Fin 6) (t : K) :
    companionDiagram K (selectedWeightCompanionX .E6 K i t) =
      selectedWeightCompanionX .E6 K (simpleNode i) t := by
  change dualCompanionEquiv K (dualCompanionDiagram K
    ((dualCompanionEquiv K).symm (selectedWeightCompanionX .E6 K i t))) = _
  rw [← dualCompanionEquiv_X K i t, MulEquiv.symm_apply_apply,
    dualCompanionDiagram_X, baseDiagram_index, dualCompanionEquiv_X]

@[simp] theorem companionDiagram_Y (i : Fin 6) (t : K) :
    companionDiagram K (selectedWeightCompanionY .E6 K i t) =
      selectedWeightCompanionY .E6 K (simpleNode i) t := by
  change dualCompanionEquiv K (dualCompanionDiagram K
    ((dualCompanionEquiv K).symm (selectedWeightCompanionY .E6 K i t))) = _
  rw [← dualCompanionEquiv_Y K i t, MulEquiv.symm_apply_apply,
    dualCompanionDiagram_Y, baseDiagram_index, dualCompanionEquiv_Y]

theorem companionDiagram_rho (g : SelectedWeightCompanion .E6 K) :
    selectedWeightCompanionRho .E6 K (companionDiagram K g) =
      adjointDiagram K (selectedWeightCompanionRho .E6 K g) := by
  obtain ⟨g, rfl⟩ := (dualCompanionEquiv K).surjective g
  simp only [companionDiagram, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    dualCompanionEquiv_rho, dualCompanionDiagram_rho]

variable {K} {L : Type*} [Field L]

/-- The integral graph action commutes with arbitrary field coefficient maps. -/
theorem companionDiagram_map (φ : K →+* L) (g : SelectedWeightCompanion .E6 K) :
    weightCompanionMap (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) φ (companionDiagram K g) =
    companionDiagram L (weightCompanionMap (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) φ g) := by
  let f := weightCompanionMap (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) φ
  have hmapX (i : Fin 6) (t : K) : f (selectedWeightCompanionX .E6 K i t) =
      selectedWeightCompanionX .E6 L i (φ t) :=
    weightCompanionMap_X (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) φ ((rootDatum .E6).indexEquiv i) t
  have hmapY (i : Fin 6) (t : K) : f (selectedWeightCompanionY .E6 K i t) =
      selectedWeightCompanionY .E6 L i (φ t) :=
    weightCompanionMap_Y (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) φ ((rootDatum .E6).indexEquiv i) t
  change f (companionDiagram K g) = companionDiagram L (f g)
  induction g using weightCompanion_induction with
  | hx i t =>
    obtain ⟨j, rfl⟩ := (rootDatum .E6).indexEquiv.surjective i
    change f (companionDiagram K (selectedWeightCompanionX .E6 K j t)) =
      companionDiagram L (f (selectedWeightCompanionX .E6 K j t))
    rw [companionDiagram_X, hmapX, hmapX, companionDiagram_X]
  | hy i t =>
    obtain ⟨j, rfl⟩ := (rootDatum .E6).indexEquiv.surjective i
    change f (companionDiagram K (selectedWeightCompanionY .E6 K j t)) =
      companionDiagram L (f (selectedWeightCompanionY .E6 K j t))
    rw [companionDiagram_Y, hmapY, hmapY, companionDiagram_Y]
  | hone => simp only [map_one]
  | hmul g h hg hh => simp only [map_mul, hg, hh]
  | hinv g hg => simp only [map_inv, hg]

end Atlas.Chevalley.TwistedE6
