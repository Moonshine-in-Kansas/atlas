import Atlas.LinearGroups.F4.Simplicity
import Atlas.LinearGroups.F4.Order
import Atlas.LinearGroups.F4.PointCount
import Atlas.LinearGroups.F4.LinearAction
import Atlas.LinearGroups.F4.FieldRootTransport
import Atlas.LinearGroups.F4.LocalRadicals
import Atlas.LinearGroups.F4.Center
import Atlas.LinearGroups.F4.RadicalFiltration
import Mathlib.FieldTheory.Finite.GaloisField

/-! Public package for the actual full split Albert polynomial-and-unit
stabilizer. This file is integrated only after its imported proofs compile
and the separate order, geometry and simplicity audits succeed. -/
noncomputable section
namespace Atlas
open scoped Pointwise

/-- The concrete F₄ construction has no finite-field simplicity exceptions. -/
structure TypeF4Construction (F : Type u) [Field F] [Finite F] : Prop where
  finite : Finite (F4.Model F)
  order : Nat.card (F4.Model F)=Nat.card F^24*(Nat.card F^12-1)*
    (Nat.card F^8-1)*(Nat.card F^6-1)*(Nat.card F^2-1)
  simple : IsSimpleGroup (F4.Model F)
  center : Subgroup.center (F4.Model F)=⊥
  root_transport : ∀ {K : Type u} [Field K] (f : F ≃+* K) (r : F4.RootData.Root) (t : F),
    F4.fieldTransport f (F4.root r t) = F4.root r (f t)
  point_transport_equivariant : ∀ {K : Type u} [Field K] (f : F ≃+* K)
    (g : F4.Model F) (x : F4.WhiteZeroPoints F),
      F4.fieldPointTransport f (g • x)=F4.fieldTransport f g • F4.fieldPointTransport f x
  point_transport_marked : ∀ {K : Type u} [Field K] (f : F ≃+* K),
    F4.fieldPointTransport f (F4.parabolicPoint (F:=F))=F4.parabolicPoint (F:=K)
  parabolic_transport : ∀ {K : Type u} [Field K] (f : F ≃+* K) (g : F4.Model F),
    F4.fieldTransport f g∈F4.parabolicPointStabilizer (F:=K) ↔
      g∈F4.parabolicPointStabilizer (F:=F)
  nonabelian : ∃ g h : F4.Model F, g*h≠h*g
  perfect : Group.IsPerfect (F4.Model F)
  faithful_linear : FaithfulSMul (F4.Model F) (Albert.Carrier F)
  faithful_points : FaithfulSMul (F4.Model F) (F4.WhiteZeroPoints F)
  transitive : MulAction.IsPretransitive (F4.Model F) (F4.WhiteZeroPoints F)
  primitive : MulAction.IsPreprimitive (F4.Model F) (F4.WhiteZeroPoints F)
  points : Nat.card (F4.WhiteZeroPoints F)=
    ((Nat.card F^12-1)*(Nat.card F^4+1))/(Nat.card F-1)
  generated : F4.rootGenerated (F:=F)=⊤
  radical_order : Nat.card (F4.radicalSubgroup (F:=F))=Nat.card F^15
  radical_solvable : Group.IsSolvable (F4.radicalSubgroup (F:=F))
  radical_seven_injective : Function.Injective (F4.radicalSevenEmbedding (F:=F))
  radical_eight_surjective : Function.Surjective (F4.radicalEightProjection (F:=F))
  radical_exact : (F4.radicalEightProjection (F:=F)).ker=
    (F4.radicalSevenEmbedding (F:=F)).range
  radical_normal : ((F4.radicalSubgroup (F:=F)).subgroupOf
    (MulAction.stabilizer (F4.Model F) (F4.parabolicPoint (F := F)))).Normal
  radical_generates : Subgroup.normalClosure
    (F4.radicalSubgroup (F:=F) : Set (F4.Model F))=⊤
  local_order : ∀ x : F4.WhiteZeroPoints F,Nat.card (F4.localRadical x)=Nat.card F^15
  local_solvable : ∀ x : F4.WhiteZeroPoints F,Group.IsSolvable (F4.localRadical x)
  local_normal : ∀ x : F4.WhiteZeroPoints F,
    ((F4.localRadical x).subgroupOf (MulAction.stabilizer (F4.Model F) x)).Normal
  local_conjugate : ∀ (g : F4.Model F) (x : F4.WhiteZeroPoints F),
    F4.localRadical (g • x)=MulAut.conj g • F4.localRadical x
  local_generate : (⨆ x : F4.WhiteZeroPoints F,F4.localRadical x)=⊤
  parabolic_order : Nat.card (F4.parabolicPointStabilizer (F:=F))=
    Nat.card F^24*(Nat.card F-1)*(Nat.card F^2-1)*(Nat.card F^4-1)*(Nat.card F^6-1)

theorem typeF4_construction {F : Type*} [Field F] [Finite F] : TypeF4Construction F where
  finite := inferInstance
  order := F4.card_Model
  simple := F4.isSimple
  center := F4.center_eq_bot
  root_transport := F4.fieldTransport_root
  point_transport_equivariant := F4.fieldPointTransport_equivariant
  point_transport_marked := F4.fieldPointTransport_parabolicPoint
  parabolic_transport := F4.fieldTransport_mem_parabolic_iff
  nonabelian := F4.exists_mul_ne_mul
  perfect := F4.isPerfect
  faithful_linear := F4.faithful_linear
  faithful_points := inferInstance
  transitive := F4.whiteZeroPoints_transitive
  primitive := F4.whiteZeroPoints_primitive
  points := F4.card_whiteZeroPoints
  generated := F4.generated_eq_top
  radical_order := F4.card_radicalSubgroup
  radical_solvable := F4.radicalSubgroup_solvable
  radical_seven_injective := F4.radicalSevenEmbedding_injective
  radical_eight_surjective := F4.radicalEightProjection_surjective
  radical_exact := F4.radical_filtration_exact
  radical_normal := F4.radical_normal_in_pointStabilizer
  radical_generates := F4.radical_normalClosure_eq_top
  local_order := F4.localRadical_card
  local_solvable := F4.localRadical_solvable
  local_normal := F4.localRadical_normal
  local_conjugate := F4.localRadical_conj
  local_generate := F4.localRadical_iSup_eq_top
  parabolic_order := F4.card_parabolic

/-- Transport is the coefficientwise equivalence of the actual Albert models. -/
def typeF4_fieldTransport {F K : Type*} [Field F] [Field K] (f : F ≃+* K) :
    F4.Model F ≃* F4.Model K := F4.fieldTransport f

/-- Every prime power is realized using the genuine finite-field construction. -/
theorem typeF4_prime_power (p f : ℕ) (hp : p.Prime) (hf : 1≤f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F=p^f ∧ TypeF4Construction F := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p f,inferInstance,inferInstance,
    GaloisField.card p f (by omega),typeF4_construction⟩

/-- The simple group witness is the actual Albert stabilizer itself. -/
theorem exists_typeF4 {F : Type u} [Field F] [Finite F] :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      (∃ g h : G,g*h≠h*g) ∧ Nat.card G=Nat.card F^24*(Nat.card F^12-1)*
        (Nat.card F^8-1)*(Nat.card F^6-1)*(Nat.card F^2-1) ∧
      Nonempty (G ≃* F4.Model F) ∧ TypeF4Construction F :=
  ⟨F4.Model F,inferInstance,inferInstance,F4.isSimple,F4.exists_mul_ne_mul,
    F4.card_Model,⟨MulEquiv.refl _⟩,typeF4_construction⟩

theorem exists_typeF4_prime_power (p f : ℕ) (hp : p.Prime) (hf : 1≤f) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      (∃ g h : G,g*h≠h*g) ∧ Nat.card G=(p^f)^24*((p^f)^12-1)*
        ((p^f)^8-1)*((p^f)^6-1)*((p^f)^2-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  refine ⟨F4.Model (GaloisField p f),inferInstance,inferInstance,
    F4.isSimple,F4.exists_mul_ne_mul,?_⟩
  rw [F4.card_Model,hc]

end Atlas
