import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.WeightCompanionFamilyRestrictionFaithful

/-! Adjoin any actual minuscule orbit to the selected family, then descend its
matrix action through literal family restriction. No order or center theorem is used. -/
noncomputable section
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable (Φ : RootType) (S : Finset (WeightLattice (rootDatum Φ).pairing))
  (hc : ∀ i μ, μ ∈ S → weightReflection (rootDatum Φ).pairing i μ ∈ S)
  (hm : ∀ μ ∈ S, ∀ i,
    μ (corootElement (rootDatum Φ).pairing i) = -1 ∨
    μ (corootElement (rootDatum Φ).pairing i) = 0 ∨
    μ (corootElement (rootDatum Φ).pairing i) = 1)

/-- None is the added orbit; Some retains each literal selected orbit. -/
def selectedAdjoinedWeightOrbits :
    Option (SelectedOrbitIndex Φ) → Finset (WeightLattice (rootDatum Φ).pairing)
  | none => S
  | some a => selectedWeightOrbits Φ a

include hc in
theorem selectedAdjoinedWeightOrbits_closed :
    ∀ a i μ, μ ∈ selectedAdjoinedWeightOrbits Φ S a →
      weightReflection (rootDatum Φ).pairing i μ ∈ selectedAdjoinedWeightOrbits Φ S a := by
  intro a
  cases a with
  | none => exact hc
  | some a => exact selectedWeightOrbits_closed Φ a

include hm in
theorem selectedAdjoinedWeightOrbits_minuscule :
    ∀ a μ, μ ∈ selectedAdjoinedWeightOrbits Φ S a → ∀ i,
      μ (corootElement (rootDatum Φ).pairing i) = -1 ∨
      μ (corootElement (rootDatum Φ).pairing i) = 0 ∨
      μ (corootElement (rootDatum Φ).pairing i) = 1 := by
  intro a
  cases a with
  | none => exact hm
  | some a => exact selectedWeightOrbits_minuscule Φ a

variable (K : Type*) [Field K]

/-- Forgetting the added orbit is an actual isomorphism over every field.
The selected integral spanning and actual diamond providers discharge both premises. -/
def selectedWeightCompanionAdjoinOrbitEquiv :
    WeightCompanion (rootDatum Φ).pairing (rootDatum Φ).base
      (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
      (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K ≃* SelectedWeightCompanion Φ K :=
  weightCompanionFamilyRestrictionEquiv (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
    (selectedAdjoinedWeightOrbits_minuscule Φ S hm) Option.some K
    (rootDatum_simpleDiamondProducts Φ) (selectedWeightSet_spans Φ)

@[simp] theorem selectedWeightCompanionAdjoinOrbitEquiv_X (i : Fin Φ.rank) (t : K) :
    selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K
      (weightCompanionX (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
        (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K ((rootDatum Φ).indexEquiv i) t) =
      selectedWeightCompanionX Φ K i t := rfl

@[simp] theorem selectedWeightCompanionAdjoinOrbitEquiv_Y (i : Fin Φ.rank) (t : K) :
    selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K
      (weightCompanionY (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
        (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K ((rootDatum Φ).indexEquiv i) t) =
      selectedWeightCompanionY Φ K i t := rfl

/-- Literal projection to the newly adjoined matrix block. -/
def selectedAdjoinedOrbitProjection :
    WeightCompanion (rootDatum Φ).pairing (rootDatum Φ).base
      (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
      (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K →*
        (Matrix (WeightOrbit (rootDatum Φ).pairing S) (WeightOrbit (rootDatum Φ).pairing S) K)ˣ where
  toFun g := g.val.2 none
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The new orbit gives a genuine representation of the existing selected model. -/
def selectedWeightCompanionOrbitRepresentation : SelectedWeightCompanion Φ K →*
    (Matrix (WeightOrbit (rootDatum Φ).pairing S) (WeightOrbit (rootDatum Φ).pairing S) K)ˣ :=
  (selectedAdjoinedOrbitProjection Φ S hc hm K).comp
    (selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).symm.toMonoidHom

@[simp] theorem selectedWeightCompanionOrbitRepresentation_X (i : Fin Φ.rank) (t : K) :
    selectedWeightCompanionOrbitRepresentation Φ S hc hm K (selectedWeightCompanionX Φ K i t) =
      weightOrbitRootElement (rootDatum Φ).pairing S hc hm K
        ((rootDatum Φ).indexEquiv i).val (-1) (by decide) t := by
  have h : (selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).symm
      (selectedWeightCompanionX Φ K i t) =
      weightCompanionX (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
        (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K ((rootDatum Φ).indexEquiv i) t := by
    apply (selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).injective
    rw [MulEquiv.apply_symm_apply, selectedWeightCompanionAdjoinOrbitEquiv_X]
  change ((selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).symm
    (selectedWeightCompanionX Φ K i t)).val.2 none = _
  rw [h]
  rfl

@[simp] theorem selectedWeightCompanionOrbitRepresentation_Y (i : Fin Φ.rank) (t : K) :
    selectedWeightCompanionOrbitRepresentation Φ S hc hm K (selectedWeightCompanionY Φ K i t) =
      weightOrbitRootElement (rootDatum Φ).pairing S hc hm K
        ((rootDatum Φ).indexEquiv i).val 1 (by decide) t := by
  have h : (selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).symm
      (selectedWeightCompanionY Φ K i t) =
      weightCompanionY (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
        (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K ((rootDatum Φ).indexEquiv i) t := by
    apply (selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).injective
    rw [MulEquiv.apply_symm_apply, selectedWeightCompanionAdjoinOrbitEquiv_Y]
  change ((selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K).symm
    (selectedWeightCompanionY Φ K i t)).val.2 none = _
  rw [h]
  rfl

end Atlas.Chevalley
