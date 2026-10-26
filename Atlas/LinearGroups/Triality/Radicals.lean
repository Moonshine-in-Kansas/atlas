import Atlas.LinearGroups.Triality.UnipotentCharacters
import Atlas.LinearGroups.Triality.PositiveSpecializations

/-! Concrete subgroups in the orthogonal matrix carrier obtained by deleting
either simple-root coordinate. Parabolic normality is a separate obligation. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def shortRadical : Subgroup (O_DPlus 4 K) :=
  (shortRadicalKernel F K hdeg).map (unipotent F K hdeg).subtype

def longRadical : Subgroup (O_DPlus 4 K) :=
  (longRadicalKernel F K hdeg).map (unipotent F K hdeg).subtype

theorem shortRadical_mem_iff (g : O_DPlus 4 K) :
    g ∈ shortRadical F K hdeg ↔ ∃ p : PositiveParameters F K, p.a = 0 ∧ positiveMatrix F K p = g := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨unipotentParameters F K hdeg u, ?_, unipotentParameters_recover F K hdeg u⟩
    exact congrArg Multiplicative.toAdd hu
  · rintro ⟨p, hp, rfl⟩
    refine ⟨unipotentCoordinates F K hdeg p, ?_, rfl⟩
    change shortCoordinate F K hdeg (unipotentCoordinates F K hdeg p) = 1
    simp [shortCoordinate, unipotentParameters, hp]

theorem longRadical_mem_iff (g : O_DPlus 4 K) :
    g ∈ longRadical F K hdeg ↔ ∃ p : PositiveParameters F K, p.b = 0 ∧ positiveMatrix F K p = g := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨unipotentParameters F K hdeg u, ?_, unipotentParameters_recover F K hdeg u⟩
    exact congrArg Multiplicative.toAdd hu
  · rintro ⟨p, hp, rfl⟩
    refine ⟨unipotentCoordinates F K hdeg p, ?_, rfl⟩
    change longCoordinate F K hdeg (unipotentCoordinates F K hdeg p) = 1
    simp [longCoordinate, unipotentParameters, hp]

theorem shortRadical_le_unipotent : shortRadical F K hdeg ≤ unipotent F K hdeg := by
  rintro _ ⟨u, hu, rfl⟩
  exact u.property

theorem longRadical_le_unipotent : longRadical F K hdeg ≤ unipotent F K hdeg := by
  rintro _ ⟨u, hu, rfl⟩
  exact u.property

theorem card_shortRadical : Nat.card (shortRadical F K hdeg) = Nat.card F ^ 9 := by
  unfold shortRadical
  rw [← Nat.card_congr ((shortRadicalKernel F K hdeg).equivMapOfInjective
    (unipotent F K hdeg).subtype Subtype.val_injective).toEquiv]
  exact card_shortRadicalKernel F K hdeg

theorem card_longRadical : Nat.card (longRadical F K hdeg) = Nat.card F ^ 11 := by
  unfold longRadical
  rw [← Nat.card_congr ((longRadicalKernel F K hdeg).equivMapOfInjective
    (unipotent F K hdeg).subtype Subtype.val_injective).toEquiv]
  exact card_longRadicalKernel F K hdeg

end Atlas.Triality
