import Atlas.LinearGroups.Chevalley.RootType
import Atlas.LinearGroups.Chevalley.Noncommutative
import Atlas.LinearGroups.Chevalley.RootData.A
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesD
import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.E7
import Atlas.LinearGroups.Chevalley.RootData.E8
import Atlas.LinearGroups.Chevalley.RootData.SmallExceptional

/-! Canonical dispatch to the constructed integral root data of all nine types.
No group cardinality, simplicity, BN pair or recognition premise appears. -/
noncomputable section
namespace Atlas.Chevalley

local instance : Fintype E6Data.Root := Fintype.ofFinite _

/-- A concrete based integral root pairing with certified rank indexing.
The type is a packaging interface, not an assumption that any family exists:
`rootDatum` below constructs every branch from the coordinate providers. -/
structure BasedDatum (r : ℕ) where
  Root : Type
  [rootFintype : Fintype Root]
  [rootDecidableEq : DecidableEq Root]
  Space : Type
  Cospace : Type
  [spaceAddCommGroup : AddCommGroup Space]
  [cospaceAddCommGroup : AddCommGroup Cospace]
  pairing : RootPairing Root ℤ Space Cospace
  [crystallographic : pairing.IsCrystallographic]
  [reduced : pairing.IsReduced]
  base : pairing.Base
  indexEquiv : Fin r ≃ base.support

attribute [instance] BasedDatum.rootFintype BasedDatum.rootDecidableEq
  BasedDatum.spaceAddCommGroup BasedDatum.cospaceAddCommGroup
  BasedDatum.crystallographic BasedDatum.reduced

namespace BasedDatum

/-- Package an already constructed pairing/base without changing any vector or root. -/
def ofPairing {r : ℕ} {ι M N : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (e : Fin r ≃ b.support) : BasedDatum r where
  Root := ι
  rootFintype := inferInstance
  rootDecidableEq := inferInstance
  Space := M
  Cospace := N
  spaceAddCommGroup := inferInstance
  cospaceAddCommGroup := inferInstance
  pairing := P
  crystallographic := inferInstance
  reduced := inferInstance
  base := b
  indexEquiv := e

 theorem base_card {r : ℕ} (D : BasedDatum r) : Nat.card D.base.support = r := by
  rw [← Nat.card_congr D.indexEquiv, Nat.card_fin]

end BasedDatum

/-- Uniform coordinate root-data dispatcher, with unbounded classical ranks. -/
def rootDatum (Φ : RootType) : BasedDatum Φ.rank := by
  classical
  cases Φ with
  | A r hr =>
    exact BasedDatum.ofPairing (TypeAData.pairing (r + 1)) (TypeAData.base r)
      (TypeAData.baseIndexEquiv r)
  | B r hr =>
    exact BasedDatum.ofPairing (ClassicalData.pairingB (r - 1 + 1))
      (ClassicalData.baseB (r - 1))
      ((finCongr (show r = r - 1 + 1 by omega)).trans (ClassicalData.baseBIndexEquiv (r - 1)))
  | C r hr =>
    exact BasedDatum.ofPairing (ClassicalData.pairingC (r - 1 + 1))
      (ClassicalData.baseC (r - 1))
      ((finCongr (show r = r - 1 + 1 by omega)).trans (ClassicalData.baseCIndexEquiv (r - 1)))
  | D r hr =>
    exact BasedDatum.ofPairing (ClassicalData.pairingD (r - 2 + 2))
      (ClassicalData.baseD (r - 2))
      ((finCongr (show r = r - 2 + 2 by omega)).trans (ClassicalData.baseDIndexEquiv (r - 2)))
  | E6 => exact BasedDatum.ofPairing E6Data.pairing E6Data.base E6Data.baseIndexEquiv
  | E7 => exact BasedDatum.ofPairing E7Data.pairing E7Data.base E7Data.baseIndexEquiv
  | E8 => exact BasedDatum.ofPairing E8Data.pairing E8Data.base E8Data.baseIndexEquiv
  | F4 => exact BasedDatum.ofPairing F4Data.pairing F4Data.base F4Data.baseIndexEquiv
  | G2 => exact BasedDatum.ofPairing G2Data.pairing G2Data.base G2Data.baseIndexEquiv

/-- The public uniform root-generated elementary adjoint group. -/
abbrev Model (Φ : RootType) (R : Type*) [CommRing R] :=
  Adjoint (rootDatum Φ).pairing (rootDatum Φ).base R

instance modelFinite (Φ : RootType) (R : Type*) [CommRing R] [Finite R] :
    Finite (Model Φ R) := inferInstance

 theorem model_base_card (Φ : RootType) :
    Nat.card (rootDatum Φ).base.support = Φ.rank := (rootDatum Φ).base_card

instance modelBaseNonempty (Φ : RootType) : Nonempty (rootDatum Φ).base.support :=
  ⟨(rootDatum Φ).indexEquiv ⟨0, Φ.rank_pos⟩⟩

 theorem model_not_commutative (Φ : RootType) (R : Type*) [CommRing R] [Nontrivial R] :
    ¬ IsMulCommutative (Model Φ R) :=
  adjoint_not_commutative (rootDatum Φ).pairing (rootDatum Φ).base R

/-- Canonical positive simple-root parameters, indexed by the declared rank. -/
def modelX (Φ : RootType) (R : Type*) [CommRing R] (i : Fin Φ.rank) (t : R) : Model Φ R :=
  adjointX (rootDatum Φ).pairing (rootDatum Φ).base R ((rootDatum Φ).indexEquiv i) t

/-- Canonical negative simple-root parameters, indexed by the declared rank. -/
def modelY (Φ : RootType) (R : Type*) [CommRing R] (i : Fin Φ.rank) (t : R) : Model Φ R :=
  adjointY (rootDatum Φ).pairing (rootDatum Φ).base R ((rootDatum Φ).indexEquiv i) t

theorem modelX_add (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) (s t : R) :
    modelX Φ R i (s + t) = modelX Φ R i s * modelX Φ R i t :=
  adjointX_add (rootDatum Φ).pairing (rootDatum Φ).base R _ s t

theorem modelY_add (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) (s t : R) :
    modelY Φ R i (s + t) = modelY Φ R i s * modelY Φ R i t :=
  adjointY_add (rootDatum Φ).pairing (rootDatum Φ).base R _ s t

theorem modelX_injective (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) : Function.Injective (modelX Φ R i) :=
  adjointX_injective (rootDatum Φ).pairing (rootDatum Φ).base R _

theorem modelY_injective (Φ : RootType) (R : Type*) [CommRing R]
    (i : Fin Φ.rank) : Function.Injective (modelY Φ R i) :=
  adjointY_injective (rootDatum Φ).pairing (rootDatum Φ).base R _

variable (Φ : RootType) {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Actual coefficient transport, not recognition by group order. -/
def modelMap (φ : R →+* S) : Model Φ R →* Model Φ S :=
  adjointMap (rootDatum Φ).pairing (rootDatum Φ).base φ

 theorem modelMap_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (modelMap Φ φ) :=
  adjointMap_injective (rootDatum Φ).pairing (rootDatum Φ).base φ hφ

/-- An actual ring isomorphism transports the concrete generated models. -/
def modelEquiv (φ : R ≃+* S) : Model Φ R ≃* Model Φ S :=
  adjointEquiv (rootDatum Φ).pairing (rootDatum Φ).base φ

@[simp] theorem modelMap_x (φ : R →+* S) (i : Fin Φ.rank) (t : R) :
    modelMap Φ φ (modelX Φ R i t) = modelX Φ S i (φ t) :=
  adjointMap_x (rootDatum Φ).pairing (rootDatum Φ).base φ _ t

@[simp] theorem modelMap_y (φ : R →+* S) (i : Fin Φ.rank) (t : R) :
    modelMap Φ φ (modelY Φ R i t) = modelY Φ S i (φ t) :=
  adjointMap_y (rootDatum Φ).pairing (rootDatum Φ).base φ _ t

@[simp] theorem modelMap_id : modelMap Φ (RingHom.id R) = MonoidHom.id _ :=
  adjointMap_id (rootDatum Φ).pairing (rootDatum Φ).base

theorem modelMap_comp (φ : R →+* S) (ψ : S →+* T) :
    modelMap Φ (ψ.comp φ) = (modelMap Φ ψ).comp (modelMap Φ φ) :=
  adjointMap_comp (rootDatum Φ).pairing (rootDatum Φ).base φ ψ

@[simp] theorem modelEquiv_x (φ : R ≃+* S) (i : Fin Φ.rank) (t : R) :
    modelEquiv Φ φ (modelX Φ R i t) = modelX Φ S i (φ t) :=
  adjointEquiv_x (rootDatum Φ).pairing (rootDatum Φ).base φ _ t

@[simp] theorem modelEquiv_y (φ : R ≃+* S) (i : Fin Φ.rank) (t : R) :
    modelEquiv Φ φ (modelY Φ R i t) = modelY Φ S i (φ t) :=
  adjointEquiv_y (rootDatum Φ).pairing (rootDatum Φ).base φ _ t

@[simp] theorem modelEquiv_refl : modelEquiv Φ (RingEquiv.refl R) = MulEquiv.refl _ :=
  adjointEquiv_refl (rootDatum Φ).pairing (rootDatum Φ).base

theorem modelEquiv_trans (φ : R ≃+* S) (ψ : S ≃+* T) :
    modelEquiv Φ (φ.trans ψ) = (modelEquiv Φ φ).trans (modelEquiv Φ ψ) :=
  adjointEquiv_trans (rootDatum Φ).pairing (rootDatum Φ).base φ ψ

end Atlas.Chevalley
