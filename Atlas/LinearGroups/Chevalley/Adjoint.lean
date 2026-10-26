import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The root-generated elementary adjoint group. This is a concrete subgroup
of matrix units constructed from integral Geck operators, without an order,
simplicity, recognition, or comparison assumption. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Positive and negative simple-root elements in the adjoint representation. -/
def adjointGenerators : Set (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
  {g | (∃ i t, g = raisingRootElement P b R i t) ∨
    (∃ i t, g = loweringRootElement P b R i t)}

/-- The elementary subgroup, not the full automorphism group or full adjoint rational group. -/
def adjointSubgroup : Subgroup (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
  Subgroup.closure (adjointGenerators P b R)

/-- The actual root-generated adjoint elementary group. -/
abbrev Adjoint := ↥(adjointSubgroup P b R)

 theorem raising_mem_adjoint (i : b.support) (t : R) :
    raisingRootElement P b R i t ∈ adjointSubgroup P b R :=
  Subgroup.subset_closure (Or.inl ⟨i, t, rfl⟩)

 theorem lowering_mem_adjoint (i : b.support) (t : R) :
    loweringRootElement P b R i t ∈ adjointSubgroup P b R :=
  Subgroup.subset_closure (Or.inr ⟨i, t, rfl⟩)

/-- Raising root element as an element of the constructed group itself. -/
def adjointX (i : b.support) (t : R) : Adjoint P b R :=
  ⟨raisingRootElement P b R i t, raising_mem_adjoint P b R i t⟩

/-- Lowering root element as an element of the constructed group itself. -/
def adjointY (i : b.support) (t : R) : Adjoint P b R :=
  ⟨loweringRootElement P b R i t, lowering_mem_adjoint P b R i t⟩

 theorem adjointX_add (i : b.support) (s t : R) :
    adjointX P b R i (s+t) = adjointX P b R i s * adjointX P b R i t := by
  apply Subtype.ext
  exact Units.ext (raisingExponential_add P b R i s t)

 theorem adjointY_add (i : b.support) (s t : R) :
    adjointY P b R i (s+t) = adjointY P b R i s * adjointY P b R i t := by
  apply Subtype.ext
  exact loweringRootElement_add P b R i s t

 theorem adjointX_injective (i : b.support) : Function.Injective (adjointX P b R i) := by
  intro s t h
  exact raisingRootElement_injective P b R i (congrArg Subtype.val h)

 theorem adjointY_injective (i : b.support) : Function.Injective (adjointY P b R i) := by
  intro s t h
  exact loweringRootElement_injective P b R i (congrArg Subtype.val h)

/-- The universal generation characterization of the actual elementary subgroup. -/
 theorem adjointSubgroup_le_iff (H : Subgroup (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ) :
    adjointSubgroup P b R ≤ H ↔
      (∀ i t, raisingRootElement P b R i t ∈ H) ∧
      (∀ i t, loweringRootElement P b R i t ∈ H) := by
  change Subgroup.closure _ ≤ H ↔ _
  rw [Subgroup.closure_le]
  constructor
  · intro h
    exact ⟨fun i t => h (Or.inl ⟨i,t,rfl⟩), fun i t => h (Or.inr ⟨i,t,rfl⟩)⟩
  · rintro ⟨hx,hy⟩ g (⟨i,t,rfl⟩ | ⟨i,t,rfl⟩)
    · exact hx i t
    · exact hy i t

/-- Every element is generated from the two families of actual simple-root elements. -/
 theorem adjoint_induction {C : Adjoint P b R → Prop}
    (hx : ∀ i t, C (adjointX P b R i t))
    (hy : ∀ i t, C (adjointY P b R i t))
    (hone : C 1) (hmul : ∀ g h, C g → C h → C (g*h))
    (hinv : ∀ g, C g → C g⁻¹) (g : Adjoint P b R) : C g := by
  rcases g with ⟨g,hg⟩
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · exact hx i t
    · exact hy i t
  | one => exact hone
  | mul a c ha hc ih₁ ih₂ => exact hmul ⟨a,ha⟩ ⟨c,hc⟩ ih₁ ih₂
  | inv a ha ih => exact hinv ⟨a,ha⟩ ih

/-- Agreement on the actual root parametrizations determines every group homomorphism. -/
 theorem adjointHom_ext {H : Type*} [Group H] (f g : Adjoint P b R →* H)
    (hx : ∀ i t, f (adjointX P b R i t) = g (adjointX P b R i t))
    (hy : ∀ i t, f (adjointY P b R i t) = g (adjointY P b R i t)) : f = g := by
  ext a
  refine adjoint_induction P b R (C := fun a => f a = g a) hx hy ?_ ?_ ?_ a
  · simp
  · intro a c ha hc
    simp only [map_mul, ha, hc]
  · intro a ha
    simp only [map_inv, ha]

/-- Explicit lifts of both root families prove surjectivity. This will apply to
restriction from a separately constructed simply connected direct-sum module. -/
 theorem adjointHom_surjective_of_root_lifts {H : Type*} [Group H]
    (f : H →* Adjoint P b R) (x y : b.support → R → H)
    (hx : ∀ i t, f (x i t) = adjointX P b R i t)
    (hy : ∀ i t, f (y i t) = adjointY P b R i t) : Function.Surjective f := by
  intro a
  apply adjoint_induction P b R (C := fun a => ∃ h, f h = a)
  · exact fun i t => ⟨x i t, hx i t⟩
  · exact fun i t => ⟨y i t, hy i t⟩
  · exact ⟨1, map_one f⟩
  · rintro a c ⟨h,rfl⟩ ⟨k,rfl⟩
    exact ⟨h*k, map_mul f h k⟩
  · rintro a ⟨h,rfl⟩
    exact ⟨h⁻¹, map_inv f h⟩

/-- Finite coefficients yield an actual finite group, without an assumed target order. -/
instance adjointFinite [Finite R] : Finite (Adjoint P b R) :=
  Finite.of_injective (fun g : Adjoint P b R => g.val.val)
    (fun _ _ h => Subtype.ext (Units.ext h))

/-- The faithful action on the actual adjoint module by invertible linear maps. -/
def adjointLinearRepresentation :
    Adjoint P b R →* LinearMap.GeneralLinearGroup R ((b.support ⊕ ι) → R) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (adjointSubgroup P b R).subtype

 theorem adjointLinearRepresentation_injective :
    Function.Injective (adjointLinearRepresentation P b R) := by
  intro g h he
  exact Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective he)

variable {R} {S T : Type*} [CommRing S] [CommRing T]

/-- Entrywise transport of invertible matrices along a coefficient homomorphism. -/
def adjointUnitsMap (φ : R →+* S) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ →*
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ :=
  Units.map φ.mapMatrix.toMonoidHom

omit [P.IsReduced] in
 theorem raisingExponential_map (φ : R →+* S) (i : b.support) (t : R) :
    (raisingExponential P b R i t).map φ = raisingExponential P b S i (φ t) := by
  ext row col
  simp [raisingExponential, Matrix.sum_apply, Matrix.smul_apply, raisingDividedOver,
    smul_eq_mul]

omit [P.IsReduced] in
 theorem loweringExponential_map (φ : R →+* S) (i : b.support) (t : R) :
    (loweringExponential P b R i t).map φ = loweringExponential P b S i (φ t) := by
  ext row col
  simp [loweringExponential, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

 theorem adjointUnitsMap_raising (φ : R →+* S) (i : b.support) (t : R) :
    adjointUnitsMap P b φ (raisingRootElement P b R i t) =
      raisingRootElement P b S i (φ t) := by
  apply Units.ext
  exact raisingExponential_map P b φ i t

 theorem adjointUnitsMap_lowering (φ : R →+* S) (i : b.support) (t : R) :
    adjointUnitsMap P b φ (loweringRootElement P b R i t) =
      loweringRootElement P b S i (φ t) := by
  apply Units.ext
  change ((loweringRootElement P b R i t).val).map φ = _
  rw [loweringRootElement_val, loweringRootElement_val]
  exact loweringExponential_map P b φ i t

 theorem adjointUnitsMap_mem (φ : R →+* S) {g}
    (hg : g ∈ adjointSubgroup P b R) :
    adjointUnitsMap P b φ g ∈ adjointSubgroup P b S := by
  have h : adjointSubgroup P b R ≤ (adjointSubgroup P b S).comap (adjointUnitsMap P b φ) := by
    rw [adjointSubgroup_le_iff]
    constructor
    · intro i t
      change adjointUnitsMap P b φ _ ∈ adjointSubgroup P b S
      rw [adjointUnitsMap_raising]
      exact raising_mem_adjoint P b S i (φ t)
    · intro i t
      change adjointUnitsMap P b φ _ ∈ adjointSubgroup P b S
      rw [adjointUnitsMap_lowering]
      exact lowering_mem_adjoint P b S i (φ t)
  exact h hg

/-- Functorial scalar transport on the concrete generated subgroups. -/
def adjointMap (φ : R →+* S) : Adjoint P b R →* Adjoint P b S where
  toFun g := ⟨adjointUnitsMap P b φ g.val, adjointUnitsMap_mem P b φ g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

 theorem adjointMap_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (adjointMap P b φ) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  ext row col
  apply hφ
  exact congrArg (fun a : Adjoint P b S => a.val.val row col) he

@[simp] theorem adjointMap_x (φ : R →+* S) (i : b.support) (t : R) :
    adjointMap P b φ (adjointX P b R i t) = adjointX P b S i (φ t) :=
  Subtype.ext (adjointUnitsMap_raising P b φ i t)

@[simp] theorem adjointMap_y (φ : R →+* S) (i : b.support) (t : R) :
    adjointMap P b φ (adjointY P b R i t) = adjointY P b S i (φ t) :=
  Subtype.ext (adjointUnitsMap_lowering P b φ i t)

@[simp] theorem adjointMap_id : adjointMap P b (RingHom.id R) = MonoidHom.id _ := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rfl

 theorem adjointMap_comp (φ : R →+* S) (ψ : S →+* T) :
    adjointMap P b (ψ.comp φ) = (adjointMap P b ψ).comp (adjointMap P b φ) := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rfl

/-- An explicit coefficient isomorphism induces an explicit group isomorphism. -/
def adjointEquiv (φ : R ≃+* S) : Adjoint P b R ≃* Adjoint P b S where
  toFun := adjointMap P b φ.toRingHom
  invFun := adjointMap P b φ.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext row col
    exact φ.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext row col
    exact φ.apply_symm_apply _
  map_mul' := (adjointMap P b φ.toRingHom).map_mul

@[simp] theorem adjointEquiv_x (φ : R ≃+* S) (i : b.support) (t : R) :
    adjointEquiv P b φ (adjointX P b R i t) = adjointX P b S i (φ t) :=
  adjointMap_x P b φ.toRingHom i t

@[simp] theorem adjointEquiv_y (φ : R ≃+* S) (i : b.support) (t : R) :
    adjointEquiv P b φ (adjointY P b R i t) = adjointY P b S i (φ t) :=
  adjointMap_y P b φ.toRingHom i t

@[simp] theorem adjointEquiv_refl : adjointEquiv P b (RingEquiv.refl R) = MulEquiv.refl _ := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rfl

 theorem adjointEquiv_trans (φ : R ≃+* S) (ψ : S ≃+* T) :
    adjointEquiv P b (φ.trans ψ) = (adjointEquiv P b φ).trans (adjointEquiv P b ψ) := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rfl

end Atlas.Chevalley
