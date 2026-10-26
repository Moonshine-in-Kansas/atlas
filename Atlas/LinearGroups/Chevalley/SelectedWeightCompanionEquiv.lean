import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.WeightCompanionEquiv

/-! Explicit coefficient transport for the actual all-type selected companion. -/
noncomputable section
namespace Atlas.Chevalley
variable (Φ : RootType) {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Apply the given coefficient isomorphism to every actual block. -/
def selectedWeightCompanionEquiv (φ : R ≃+* S) :
    SelectedWeightCompanion Φ R ≃* SelectedWeightCompanion Φ S :=
  weightCompanionEquiv (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) φ

@[simp] theorem selectedWeightCompanionEquiv_X (φ : R ≃+* S)
    (i : Fin Φ.rank) (t : R) :
    selectedWeightCompanionEquiv Φ φ (selectedWeightCompanionX Φ R i t) =
      selectedWeightCompanionX Φ S i (φ t) :=
  weightCompanionEquiv_X (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) φ ((rootDatum Φ).indexEquiv i) t

@[simp] theorem selectedWeightCompanionEquiv_Y (φ : R ≃+* S)
    (i : Fin Φ.rank) (t : R) :
    selectedWeightCompanionEquiv Φ φ (selectedWeightCompanionY Φ R i t) =
      selectedWeightCompanionY Φ S i (φ t) :=
  weightCompanionEquiv_Y (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) φ ((rootDatum Φ).indexEquiv i) t

theorem selectedWeightCompanionEquiv_rho (φ : R ≃+* S)
    (g : SelectedWeightCompanion Φ R) :
    selectedWeightCompanionRho Φ S (selectedWeightCompanionEquiv Φ φ g) =
      modelEquiv Φ φ (selectedWeightCompanionRho Φ R g) := rfl

theorem selectedWeightCompanionEquiv_rho_comp (φ : R ≃+* S) :
    (selectedWeightCompanionRho Φ S).comp (selectedWeightCompanionEquiv Φ φ).toMonoidHom =
      (modelEquiv Φ φ).toMonoidHom.comp (selectedWeightCompanionRho Φ R) := by
  ext g
  rfl

@[simp] theorem selectedWeightCompanionEquiv_refl :
    selectedWeightCompanionEquiv Φ (RingEquiv.refl R) =
      MulEquiv.refl (SelectedWeightCompanion Φ R) :=
  weightCompanionEquiv_refl (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ)

@[simp] theorem selectedWeightCompanionEquiv_symm (φ : R ≃+* S) :
    selectedWeightCompanionEquiv Φ φ.symm = (selectedWeightCompanionEquiv Φ φ).symm :=
  weightCompanionEquiv_symm (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) φ

theorem selectedWeightCompanionEquiv_trans (φ : R ≃+* S) (ψ : S ≃+* T) :
    selectedWeightCompanionEquiv Φ (φ.trans ψ) =
      (selectedWeightCompanionEquiv Φ φ).trans (selectedWeightCompanionEquiv Φ ψ) :=
  weightCompanionEquiv_trans (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) φ ψ

end Atlas.Chevalley
