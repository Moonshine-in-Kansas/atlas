import Atlas.LinearGroups.Chevalley.WeightCompanionTransport

/-! Explicit coefficient-ring isomorphism transport of the actual companion. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  {R S : Type*} [CommRing R] [CommRing S]

/-- The inverse is the already constructed transport along the inverse ring map. -/
def weightCompanionEquiv (φ : R ≃+* S) :
    WeightCompanion P b O hclosed hmin R ≃* WeightCompanion P b O hclosed hmin S where
  toFun := weightCompanionMap P b O hclosed hmin φ.toRingHom
  invFun := weightCompanionMap P b O hclosed hmin φ.symm.toRingHom
  left_inv g := by
    have he := weightCompanionMap_comp P b O hclosed hmin φ.toRingHom φ.symm.toRingHom
    have hid : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id R := by ext x; exact φ.symm_apply_apply x
    rw [hid, weightCompanionMap_id] at he
    exact (congrArg (fun f => f g) he).symm
  right_inv g := by
    have he := weightCompanionMap_comp P b O hclosed hmin φ.symm.toRingHom φ.toRingHom
    have hid : φ.toRingHom.comp φ.symm.toRingHom = RingHom.id S := by ext x; exact φ.apply_symm_apply x
    rw [hid, weightCompanionMap_id] at he
    exact (congrArg (fun f => f g) he).symm
  map_mul' := (weightCompanionMap P b O hclosed hmin φ.toRingHom).map_mul

@[simp] theorem weightCompanionEquiv_X (φ : R ≃+* S) (i : b.support) (t : R) :
    weightCompanionEquiv P b O hclosed hmin φ (weightCompanionX P b O hclosed hmin R i t) =
      weightCompanionX P b O hclosed hmin S i (φ t) :=
  weightCompanionMap_X P b O hclosed hmin φ.toRingHom i t

@[simp] theorem weightCompanionEquiv_Y (φ : R ≃+* S) (i : b.support) (t : R) :
    weightCompanionEquiv P b O hclosed hmin φ (weightCompanionY P b O hclosed hmin R i t) =
      weightCompanionY P b O hclosed hmin S i (φ t) :=
  weightCompanionMap_Y P b O hclosed hmin φ.toRingHom i t

theorem weightCompanionEquiv_rho (φ : R ≃+* S) (g : WeightCompanion P b O hclosed hmin R) :
    weightCompanionRho P b O hclosed hmin S (weightCompanionEquiv P b O hclosed hmin φ g) =
      adjointEquiv P b φ (weightCompanionRho P b O hclosed hmin R g) := rfl

@[simp] theorem weightCompanionEquiv_apply (φ : R ≃+* S)
    (g : WeightCompanion P b O hclosed hmin R) :
    weightCompanionEquiv P b O hclosed hmin φ g =
      weightCompanionMap P b O hclosed hmin φ.toRingHom g := rfl

@[simp] theorem weightCompanionEquiv_refl :
    weightCompanionEquiv P b O hclosed hmin (RingEquiv.refl R) =
      MulEquiv.refl (WeightCompanion P b O hclosed hmin R) := by
  apply MulEquiv.ext
  intro g
  exact congrArg (fun f => f g) (weightCompanionMap_id P b O hclosed hmin (R := R))

@[simp] theorem weightCompanionEquiv_symm (φ : R ≃+* S) :
    weightCompanionEquiv P b O hclosed hmin φ.symm =
      (weightCompanionEquiv P b O hclosed hmin φ).symm := by
  apply MulEquiv.ext
  intro g
  rfl

/-- Composition acts on every actual matrix coefficient in the specified order. -/
theorem weightCompanionEquiv_trans {T : Type*} [CommRing T]
    (φ : R ≃+* S) (ψ : S ≃+* T) :
    weightCompanionEquiv P b O hclosed hmin (φ.trans ψ) =
      (weightCompanionEquiv P b O hclosed hmin φ).trans
        (weightCompanionEquiv P b O hclosed hmin ψ) := by
  apply MulEquiv.ext
  intro g
  exact congrArg (fun f => f g)
    (weightCompanionMap_comp P b O hclosed hmin φ.toRingHom ψ.toRingHom)

@[simp] theorem weightCompanionEquiv_symm_X (φ : R ≃+* S) (i : b.support) (t : S) :
    (weightCompanionEquiv P b O hclosed hmin φ).symm
      (weightCompanionX P b O hclosed hmin S i t) =
      weightCompanionX P b O hclosed hmin R i (φ.symm t) :=
  weightCompanionMap_X P b O hclosed hmin φ.symm.toRingHom i t

@[simp] theorem weightCompanionEquiv_symm_Y (φ : R ≃+* S) (i : b.support) (t : S) :
    (weightCompanionEquiv P b O hclosed hmin φ).symm
      (weightCompanionY P b O hclosed hmin S i t) =
      weightCompanionY P b O hclosed hmin R i (φ.symm t) :=
  weightCompanionMap_Y P b O hclosed hmin φ.symm.toRingHom i t

/-- Naturality as an equality of actual group homomorphisms. -/
theorem weightCompanionEquiv_rho_comp (φ : R ≃+* S) :
    (weightCompanionRho P b O hclosed hmin S).comp
        (weightCompanionEquiv P b O hclosed hmin φ).toMonoidHom =
      (adjointEquiv P b φ).toMonoidHom.comp
        (weightCompanionRho P b O hclosed hmin R) := by
  apply MonoidHom.ext
  intro g
  rfl

end Atlas.Chevalley
