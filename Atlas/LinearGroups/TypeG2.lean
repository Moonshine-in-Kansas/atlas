import Atlas.LinearGroups.G2.Simplicity
import Atlas.LinearGroups.G2.BinaryException
import Atlas.LinearGroups.G2.Order
import Atlas.LinearGroups.G2.LocalFieldTransport
import Atlas.LinearGroups.G2.LocalProperties
import Mathlib.FieldTheory.Finite.GaloisField

noncomputable section
namespace Atlas

/-- The complete family concerns the full automorphism group of the actual split octonions. -/
structure TypeG2Construction (F : Type*) [Field F] : Prop where
  finite : Finite (G2.Model F)
  order : Nat.card (G2.Model F) = Nat.card F^6 * (Nat.card F^6-1) * (Nat.card F^2-1)
  simple_iff : IsSimpleGroup (G2.Model F) ↔ 2 < Nat.card F
  nonabelian : ∃ g h : G2.Model F,g*h ≠ h*g
  faithful_linear : FaithfulSMul (G2.Model F) (SplitOctonion.Carrier F)
  faithful : FaithfulSMul (G2.Model F) (G2.SingularPoints F)
  transitive : MulAction.IsPretransitive (G2.Model F) (G2.SingularPoints F)
  primitive : MulAction.IsPreprimitive (G2.Model F) (G2.SingularPoints F)
  points : Nat.card (G2.SingularPoints F) = (Nat.card F^6-1)/(Nat.card F-1)
  generated : G2.generated (F := F) = ⊤
  local_order : ∀ p : G2.SingularPoints F,Nat.card (G2.localAt p) = Nat.card F^2
  local_abelian : ∀ p : G2.SingularPoints F,IsMulCommutative (G2.localAt p)
  local_generate : 2 < Nat.card F → (⨆ p : G2.SingularPoints F,G2.localAt p) = ⊤
  perfect : 2 < Nat.card F → Group.IsPerfect (G2.Model F)
  binary_normal : (G2.longRootNormalClosure (F := F)).Normal
  binary_order : Nat.card F = 2 → Nat.card (G2.longRootNormalClosure (F := F)) = 6048
  binary_index : Nat.card F = 2 → (G2.longRootNormalClosure (F := F)).index = 2

end Atlas

namespace Atlas

theorem typeG2_construction {F : Type*} [Field F] [Finite F] : TypeG2Construction F where
  finite := inferInstance
  order := G2.card_Model
  simple_iff := G2.isSimple_iff
  nonabelian := G2.exists_mul_ne_mul
  faithful_linear := inferInstance
  faithful := inferInstance
  transitive := inferInstance
  primitive := G2.singularPoints_primitive
  points := G2.card_singularPoints F
  generated := G2.generated_eq_top
  local_order := G2.card_localAt
  local_abelian := G2.localAt_commutative
  local_generate hq := G2.localAt_iSup_eq_normalClosure.trans (G2.longRootNormalClosure_eq_top hq)
  perfect := G2.isPerfect
  binary_normal := inferInstance
  binary_order := G2.card_longRootNormalClosure_binary
  binary_index := G2.index_longRootNormalClosure_binary

/-- Every finite field yields the concrete construction, including its binary exception. -/
theorem typeG2_prime_power (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p^f ∧ TypeG2Construction F := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p f,inferInstance,inferInstance,
    GaloisField.card p f (by omega),typeG2_construction⟩

/-- The simple-group existence witness is the actual octonion automorphism model. -/
theorem exists_typeG2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      (∃ g h : G,g*h ≠ h*g) ∧
      Nat.card G = Nat.card F^6*(Nat.card F^6-1)*(Nat.card F^2-1) ∧
      Nonempty (G ≃* G2.Model F) ∧ TypeG2Construction F :=
  ⟨G2.Model F,inferInstance,inferInstance,G2.isSimple hq,G2.exists_mul_ne_mul,
    G2.card_Model,⟨MulEquiv.refl _⟩,typeG2_construction⟩

end Atlas

namespace Atlas
/-- Every nonbinary prime-power parameter has a simple noncommutative group
witnessed by the concrete split-octonion model over its Galois field. -/
theorem exists_typeG2_prime_power (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hq : 2 < p^f) : ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      (∃ g h : G,g*h ≠ h*g) ∧ Nat.card G = (p^f)^6*((p^f)^6-1)*((p^f)^2-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  refine ⟨G2.Model (GaloisField p f),inferInstance,inferInstance,
    G2.isSimple (by simpa only [hc] using hq),G2.exists_mul_ne_mul,?_⟩
  rw [G2.card_Model,hc]
end Atlas
