import Atlas.LinearGroups.ReeG2.Simplicity
import Atlas.LinearGroups.ReeG2.FieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

noncomputable section
namespace Atlas

/-- Public facts about the actual Tits-twisted seven-dimensional matrix group. -/
structure TypeReeG2Construction (F : Type*) [Field F] [Finite F] [CharP F 3]
    (m : ℕ) (hp : ReeG2.Parameters F m) : Prop where
  finite : Finite (ReeG2.Model F m)
  order : Nat.card (ReeG2.Model F m) = Nat.card F^3 * (Nat.card F^3+1) * (Nat.card F-1)
  simple : IsSimpleGroup (ReeG2.Model F m)
  nonabelian : ∃ g h : ReeG2.Model F m, g*h ≠ h*g
  perfect : Group.IsPerfect (ReeG2.Model F m)
  points : Nat.card (ReeG2.pointSet (F := F) m) = Nat.card F^3+1
  root_order : Nat.card (ReeG2.rootSubgroup m hp.cardinality) = Nat.card F^3
  stabilizer_order : Nat.card (ReeG2.borel m hp.cardinality) = Nat.card F^3*(Nat.card F-1)
  faithful : letI := ReeG2.pointAction m hp.cardinality
    FaithfulSMul (ReeG2.Model F m) (ReeG2.pointSet (F := F) m)
  doubly_transitive : letI := ReeG2.pointAction m hp.cardinality
    MulAction.IsMultiplyPretransitive (ReeG2.Model F m) (ReeG2.pointSet (F := F) m) 2
  primitive : letI := ReeG2.pointAction m hp.cardinality
    MulAction.IsPreprimitive (ReeG2.Model F m) (ReeG2.pointSet (F := F) m)

namespace ReeG2
theorem finite_model (F : Type*) [Field F] [Finite F] [CharP F 3] (m : ℕ) :
    Finite (Model F m) := inferInstance
end ReeG2

theorem typeReeG2_construction {F : Type*} [Field F] [Finite F] [CharP F 3]
    (m : ℕ) (hp : ReeG2.Parameters F m) : TypeReeG2Construction F m hp where
  finite := inferInstance
  order := ReeG2.order m hp.cardinality
  simple := ReeG2.simple m hp
  nonabelian := ReeG2.model_noncommutative m hp.cardinality
  perfect := ReeG2.perfect m hp
  points := ReeG2.card_pointSet m
  root_order := ReeG2.card_rootSubgroup m hp.cardinality
  stabilizer_order := ReeG2.card_borel m hp.cardinality
  faithful := ReeG2.pointAction_faithful m hp.cardinality
  doubly_transitive := ReeG2.pointAction_two_pretransitive m hp.cardinality
  primitive := ReeG2.pointAction_preprimitive m hp.cardinality

/-- Existence is witnessed by the same actual generated matrix model. -/
theorem exists_typeReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3]
    (m : ℕ) (hp : ReeG2.Parameters F m) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      (∃ g h : G, g*h ≠ h*g) ∧
      Nat.card G = Nat.card F^3 * (Nat.card F^3+1) * (Nat.card F-1) ∧
      Nonempty (G ≃* ReeG2.Model F m) ∧ TypeReeG2Construction F m hp :=
  ⟨ReeG2.Model F m,inferInstance,inferInstance,ReeG2.simple m hp,
    ReeG2.model_noncommutative m hp.cardinality,ReeG2.order m hp.cardinality,
    ⟨MulEquiv.refl _⟩,typeReeG2_construction m hp⟩

/-- Every public Ree parameter is realized over its canonical finite field. -/
theorem exists_typeReeG2_parameter (m : ℕ) (hm : 1 ≤ m) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      (∃ g h : G, g*h ≠ h*g) ∧
      Nat.card G = (3^(2*m+1))^3 * ((3^(2*m+1))^3+1) * (3^(2*m+1)-1) ∧
      Nonempty (G ≃* ReeG2.Model (GaloisField 3 (2*m+1)) m) := by
  have hp : ReeG2.Parameters (GaloisField 3 (2*m+1)) m :=
    ⟨hm,GaloisField.card 3 (2*m+1) (by omega)⟩
  refine ⟨ReeG2.Model (GaloisField 3 (2*m+1)) m,inferInstance,inferInstance,
    ReeG2.simple m hp,ReeG2.model_noncommutative m hp.cardinality,?_,⟨MulEquiv.refl _⟩⟩
  rw [ReeG2.order m hp.cardinality,hp.cardinality]

/-- The public model is independent of the implementation of its finite field. -/
theorem typeReeG2_field_transport {F K : Type*}
    [Field F] [Finite F] [CharP F 3] [Field K] [Finite K] [CharP K 3]
    (e : F ≃+* K) (m : ℕ) : Nonempty (ReeG2.Model F m ≃* ReeG2.Model K m) :=
  ⟨ReeG2.fieldEquiv e m⟩

end Atlas

