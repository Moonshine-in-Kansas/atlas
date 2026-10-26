import Atlas.LinearGroups.SuzukiFamily.ExactSimplicity
import Atlas.LinearGroups.SuzukiFamily.SplitBorel
import Atlas.LinearGroups.SuzukiFamily.FieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

/-! Public constructive package for the Suzuki family, distinct from sporadic Suz. -/
noncomputable section
namespace Atlas

structure TypeSuzukiConstruction (F : Type*) [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hcard : Nat.card F=2^(2*m+1)) : Prop where
  finite : Finite (SuzukiFamily.Group F m)
  order : Nat.card (SuzukiFamily.Group F m) = Nat.card F^2*(Nat.card F^2+1)*(Nat.card F-1)
  simple : IsSimpleGroup (SuzukiFamily.Group F m)
  nonabelian : ¬ IsMulCommutative (SuzukiFamily.Group F m)
  perfect : Group.IsPerfect (SuzukiFamily.Group F m)
  embedded : Function.Injective (SuzukiFamily.embedding (F := F) m)
  points : Nat.card (SuzukiFamily.pointSet (F := F) m)=Nat.card F^2+1
  root_order : Nat.card (SuzukiFamily.rootSubgroup m hcard)=Nat.card F^2
  torus_order : Nat.card (SuzukiFamily.torusSubgroup (F := F) m)=Nat.card F-1
  stabilizer_order : Nat.card (SuzukiFamily.borel m hcard)=Nat.card F^2*(Nat.card F-1)
  stabilizer_solvable : Group.IsSolvable (SuzukiFamily.borel m hcard)
  stabilizer_kernel : (SuzukiFamily.borelProjection m hcard).ker=
    (SuzukiFamily.rootIntoBorel m hcard).range
  stabilizer_split : Function.RightInverse (SuzukiFamily.borelTorusHom m hcard)
    (SuzukiFamily.borelProjection m hcard)
  faithful : letI := SuzukiFamily.pointAction m hcard
    FaithfulSMul (SuzukiFamily.Group F m) (SuzukiFamily.pointSet (F := F) m)
  doubly_transitive : letI := SuzukiFamily.pointAction m hcard
    MulAction.IsMultiplyPretransitive (SuzukiFamily.Group F m) (SuzukiFamily.pointSet (F := F) m) 2
  primitive : letI := SuzukiFamily.pointAction m hcard
    MulAction.IsPreprimitive (SuzukiFamily.Group F m) (SuzukiFamily.pointSet (F := F) m)
  normal_forms : Nonempty (SuzukiFamily.CellParameters F ≃ SuzukiFamily.Group F m)

theorem typeSuzuki_construction {F : Type*} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hcard : Nat.card F=2^(2*m+1)) (hm : 1≤m) : TypeSuzukiConstruction F m hcard where
  finite := inferInstance
  order := SuzukiFamily.card_group m hcard
  simple := SuzukiFamily.simple_of_large m hcard hm
  nonabelian := SuzukiFamily.noncommutative_of_large m hcard hm
  perfect := SuzukiFamily.perfect_of_large m hcard hm
  embedded := SuzukiFamily.embedding_injective m
  points := SuzukiFamily.card_pointSet m
  root_order := SuzukiFamily.card_rootSubgroup m hcard
  torus_order := SuzukiFamily.card_torusSubgroup m
  stabilizer_order := SuzukiFamily.card_borel m hcard
  stabilizer_solvable := SuzukiFamily.borel_solvable m hcard
  stabilizer_kernel := SuzukiFamily.borelProjection_ker_eq_root m hcard
  stabilizer_split := SuzukiFamily.borelProjection_section m hcard
  faithful := SuzukiFamily.pointAction_faithful m hcard
  doubly_transitive := SuzukiFamily.pointAction_two_pretransitive m hcard
  primitive := SuzukiFamily.pointAction_preprimitive m hcard
  normal_forms := ⟨SuzukiFamily.cellEquiv m hcard⟩

theorem exists_typeSuzuki {F : Type u} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hcard : Nat.card F=2^(2*m+1)) (hm : 1≤m) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G=Nat.card F^2*(Nat.card F^2+1)*(Nat.card F-1) ∧
      Nonempty (G ≃* SuzukiFamily.Group F m) ∧ TypeSuzukiConstruction F m hcard :=
  ⟨SuzukiFamily.Group F m,inferInstance,inferInstance,SuzukiFamily.simple_of_large m hcard hm,
    SuzukiFamily.noncommutative_of_large m hcard hm,SuzukiFamily.card_group m hcard,
    ⟨MulEquiv.refl _⟩,typeSuzuki_construction m hcard hm⟩

theorem typeSuzuki_prime_power (m : ℕ) (hm : 1≤m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hcard : Nat.card F=2^(2*m+1)), TypeSuzukiConstruction F m hcard := by
  let F := GaloisField 2 (2*m+1)
  have hc : Nat.card F=2^(2*m+1) := GaloisField.card 2 (2*m+1) (by omega)
  exact ⟨F,inferInstance,inferInstance,inferInstance,hc,typeSuzuki_construction m hc hm⟩

theorem exists_typeSuzuki_parameter (m : ℕ) (hm : 1≤m) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G=(2^(2*m+1))^2*((2^(2*m+1))^2+1)*(2^(2*m+1)-1) ∧
      Nonempty (G ≃* SuzukiFamily.Group (GaloisField 2 (2*m+1)) m) := by
  have hc := GaloisField.card 2 (2*m+1) (by omega)
  refine ⟨SuzukiFamily.Group (GaloisField 2 (2*m+1)) m,inferInstance,inferInstance,
    SuzukiFamily.simple_of_large m hc hm,SuzukiFamily.noncommutative_of_large m hc hm,?_,⟨MulEquiv.refl _⟩⟩
  rw [SuzukiFamily.card_group m hc,hc]

theorem typeSuzuki_field_transport {F K : Type*}
    [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (e : F ≃+* K) (m : ℕ) : Nonempty (SuzukiFamily.Group F m ≃* SuzukiFamily.Group K m) :=
  ⟨SuzukiFamily.fieldEquiv e m⟩
end Atlas
