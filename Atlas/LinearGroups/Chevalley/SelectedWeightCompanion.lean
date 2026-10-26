import Atlas.LinearGroups.Chevalley.SelectedWeightOrbits
import Atlas.LinearGroups.Chevalley.WeightCompanionCommutation
import Atlas.LinearGroups.Chevalley.WeightCompanionEmpty
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! The concrete selected-weight simultaneous linear
model and adjoint projection. The name deliberately does not claim that the
remaining central-kernel or simply-connectedness identifications are proved. -/
noncomputable section
namespace Atlas.Chevalley
open Classical

abbrev SelectedWeightCompanion (Φ : RootType) (R : Type*) [CommRing R] :=
  WeightCompanion (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

instance selectedWeightCompanionFinite (Φ : RootType) (R : Type*) [CommRing R] [Finite R] :
    Finite (SelectedWeightCompanion Φ R) := inferInstance

def selectedWeightCompanionRho (Φ : RootType) (R : Type*) [CommRing R] :
    SelectedWeightCompanion Φ R →* Model Φ R :=
  weightCompanionRho (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

theorem selectedWeightCompanionRho_surjective (Φ : RootType) (R : Type*) [CommRing R] :
    Function.Surjective (selectedWeightCompanionRho Φ R) :=
  weightCompanionRho_surjective (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

def selectedWeightCompanionX (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) (t : R) : SelectedWeightCompanion Φ R :=
  weightCompanionX (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ)
    R ((rootDatum Φ).indexEquiv i) t

def selectedWeightCompanionY (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) (t : R) : SelectedWeightCompanion Φ R :=
  weightCompanionY (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ)
    R ((rootDatum Φ).indexEquiv i) t

@[simp] theorem selectedWeightCompanionRho_X (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) (t : R) :
    selectedWeightCompanionRho Φ R (selectedWeightCompanionX Φ R i t) = modelX Φ R i t := rfl
@[simp] theorem selectedWeightCompanionRho_Y (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) (t : R) :
    selectedWeightCompanionRho Φ R (selectedWeightCompanionY Φ R i t) = modelY Φ R i t := rfl

abbrev SelectedCompanionCoordinates (Φ : RootType) :=
  WeightCompanionCoordinates (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)

/-- Literal finite block matrices, including the same actual adjoint summand. -/
def selectedWeightCompanionMatrixRepresentation (Φ : RootType) (R : Type*) [CommRing R] :=
  weightCompanionMatrixRepresentation (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

theorem selectedWeightCompanionMatrixRepresentation_injective
    (Φ : RootType) (R : Type*) [CommRing R] :
    Function.Injective (selectedWeightCompanionMatrixRepresentation Φ R) :=
  weightCompanionMatrixRepresentation_injective (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

/-- The three unimodular types require no extra weight block, and the actual
projection is consequently a concrete group isomorphism. -/
def selectedWeightCompanionAdjointEquivOfEmpty (Φ : RootType)
    [IsEmpty (SelectedOrbitIndex Φ)] (R : Type*) [CommRing R] :
    SelectedWeightCompanion Φ R ≃* Model Φ R :=
  weightCompanionAdjointEquivOfIsEmpty (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

end Atlas.Chevalley
