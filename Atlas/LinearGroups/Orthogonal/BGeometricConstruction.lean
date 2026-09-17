import Atlas.LinearGroups.Orthogonal.BAllRanksStructure
import Atlas.LinearGroups.Orthogonal.BGeometryAllRanks

/-! # Complete quadratic B construction with its actual singular-line geometry -/
noncomputable section
namespace Atlas
open Orthogonal
universe u

/-- The existing intrinsic construction, augmented by coordinate generation and
uniform geometry on the singular lines of the same quadratic model. -/
structure TypeBGeometricConstruction (n : ℕ) (F : Type*) [Field F] : Prop
    extends TypeBStructuralConstruction n F where
  coordinate_generation : coordinateRootSubgroupB (F := F) n = elementarySubgroup (formB n F)
  faithful : FaithfulSMul (B n F) (SingularPoints (formB n F))
  transitive : MulAction.IsPretransitive (B n F) (SingularPoints (formB n F))
  primitive_rank_ge_two : 2 ≤ n → MulAction.IsPreprimitive (B n F) (SingularPoints (formB n F))
  roots_normal_generate : ∀ p : SingularPoints (formB n F),
    Subgroup.normalClosure (projectiveRootSubgroup (formB n F) p : Set (B n F)) = ⊤

theorem typeB_geometric_construction {F : Type*} [Field F] [Finite F] (n : ℕ)
    (h : B_good n (Nat.card F)) : TypeBGeometricConstruction n F :=
  { toTypeBStructuralConstruction := typeB_structural_construction n h
    coordinate_generation := B_coordinate_roots_generate_all_rank n h.1
    faithful := B_faithful_all_rank n h.1
    transitive := B_transitive_all_rank n h.1
    primitive_rank_ge_two := B_primitive_all_char n
    roots_normal_generate := B_roots_normal_generate_all_rank n h.1 }

theorem typeB_prime_power_geometric (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (h : B_good n (p ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ TypeBGeometricConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  exact ⟨GaloisField p f, inferInstance, inferInstance, hc,
    typeB_geometric_construction n (by simpa only [hc] using h)⟩

theorem exists_typeB_geometric {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : B_good n (Nat.card F)) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = B_order n (Nat.card F) ∧ Nonempty (G ≃* B n F) ∧ TypeBGeometricConstruction n F := by
  have hc := typeB_geometric_construction (F := F) n h
  exact ⟨B n F, inferInstance, hc.finite, hc.simple, hc.nonabelian, hc.order,
    ⟨MulEquiv.refl _⟩, hc⟩
end Atlas
