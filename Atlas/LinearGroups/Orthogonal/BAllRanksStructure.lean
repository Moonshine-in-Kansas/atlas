import Atlas.LinearGroups.Orthogonal.BAllRanksConstruction
import Atlas.LinearGroups.Orthogonal.B1Structure
import Atlas.LinearGroups.Orthogonal.BGeometryInterface
import Atlas.LinearGroups.Orthogonal.BFamilyTransport
import Mathlib.GroupTheory.Index

/-! # Full positive-rank B structural package

The intrinsic subgroup is the determinant/spinor kernel in odd characteristic
and the full isometry group in characteristic two, including the exceptional
small groups. Equality with the derived subgroup is asserted only in the
advertised simple range. Scalar centers are computed independently of simplicity.
-/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem B_center_eq_bot_all_rank (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.center (elementarySubgroup (formB n F)) = ⊥ := by
  by_cases h : n = 1
  · subst n
    exact elementaryB_one_center_eq_bot
  · exact B_center_eq_bot n (by omega)

theorem B_scalar_eq_center_all_rank (n : ℕ) (hn : 1 ≤ n) :
    elementaryScalarSubgroup (formB n F) = Subgroup.center (elementarySubgroup (formB n F)) := by
  rw [B_scalar_eq_bot_all_rank n hn,B_center_eq_bot_all_rank n hn]

theorem B_center_order_all_rank (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Subgroup.center (elementarySubgroup (formB n F))) = 1 := by
  rw [B_center_eq_bot_all_rank n hn]
  exact Nat.card_unique

theorem B_elementary_card_mul_denominator_all_rank (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (elementarySubgroup (formB n F)) * B_order_denominator (Nat.card F) =
      B_order_numerator n (Nat.card F) := by
  rw [← Nat.card_congr (B_elementaryEquiv_all_rank (F := F) n hn).toEquiv]
  exact B_card_mul_denominator_all_rank n hn

theorem B_elementary_index_all_rank (n : ℕ) (hn : 1 ≤ n) :
    (elementarySubgroup (formB n F)).index =
      (if (2 : F) = 0 then 1 else 2) * B_order_denominator (Nat.card F) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := elementarySubgroup (formB n F)))
  rw [Subgroup.card_mul_index,card_fullB]
  have h := B_elementary_card_mul_denominator_all_rank (F := F) n hn
  calc
    _ = (if (2 : F) = 0 then 1 else 2) * B_order_numerator n (Nat.card F) := by
      simp only [B_order_numerator,mul_assoc]
    _ = _ := by rw [← h]; ring

theorem B_odd_intrinsic_all_rank (n : ℕ) (hn : 1 ≤ n) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB n F) = specialSubgroup (formB n F) ⊓
      (spinorNorm (formB n F) (polarB_nondegenerate h2) h2).ker := by
  by_cases h : n = 1
  · subst n
    exact elementaryB_one_eq_intrinsicKernel h2
  · exact B_odd_intrinsic n (by omega) h2

theorem B_elementary_eq_derived_all_rank (n : ℕ) (h : B_good n (Nat.card F)) :
    elementarySubgroup (formB n F) = commutator (O_B n F) := by
  apply le_antisymm
  · letI := B_elementary_perfect_all_rank n h
    rw [← Subgroup.commutator_eq_self (H := elementarySubgroup (formB n F))]
    exact Subgroup.commutator_mono le_top le_top
  · by_cases h2 : (2 : F) = 0
    · rw [B_even_intrinsic n h2]
      exact le_top
    · rw [B_odd_intrinsic_all_rank n h.1 h2,← determinantSign_kernel (formB n F) (polarB_nondegenerate h2)]
      exact le_inf (Abelianization.commutator_subset_ker (G := O_B n F) (A := rootsOfUnity 2 F) (determinantSign (formB n F) (polarB_nondegenerate h2)))
        (Abelianization.commutator_subset_ker (G := O_B n F) (A := Atlas.SquareClass F) (spinorNorm (formB n F) (polarB_nondegenerate h2) h2))

/-- Quotienting by the actual scalar subgroup is quotienting by the full center. -/
def B_quotientCenterEquiv_all_rank (n : ℕ) (hn : 1 ≤ n) :
    B n F ≃* (elementarySubgroup (formB n F) ⧸ Subgroup.center (elementarySubgroup (formB n F))) :=
  QuotientGroup.quotientMulEquivOfEq (B_scalar_eq_center_all_rank n hn)

/-- Equal-cardinality fields give isomorphic actual quadratic models in every rank. -/
theorem B_equiv_of_card_eq_all_rank {K : Type*} [Field K] [Finite K] (n : ℕ)
    (h : Nat.card F = Nat.card K) : Nonempty (B n F ≃* B n K) := by
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)
  exact ⟨B_fieldEquiv n e⟩
end Atlas.Orthogonal

namespace Atlas
open Orthogonal
universe u
/-- The uniform numerical, intrinsic-kernel, center and simple-group package.
The singular-line/root interfaces carry their separately verified rank and
characteristic guards; these are not assertions of coordinate-root generation. -/
structure TypeBStructuralConstruction (n : ℕ) (F : Type*) [Field F] : Prop
    extends TypeBAllRanksConstruction n F where
  numerator_positive : 0 < B_order_numerator n (Nat.card F)
  denominator_positive : 0 < B_order_denominator (Nat.card F)
  elementary_order_exact : Nat.card (elementarySubgroup (formB n F)) *
    B_order_denominator (Nat.card F) = B_order_numerator n (Nat.card F)
  elementary_index : (elementarySubgroup (formB n F)).index =
    (if (2 : F) = 0 then 1 else 2) * B_order_denominator (Nat.card F)
  center_trivial : Subgroup.center (elementarySubgroup (formB n F)) = ⊥
  center_order : Nat.card (Subgroup.center (elementarySubgroup (formB n F))) = 1
  scalar_equals_center : elementaryScalarSubgroup (formB n F) =
    Subgroup.center (elementarySubgroup (formB n F))
  odd_intrinsic : ∀ h2 : (2 : F) ≠ 0,
    elementarySubgroup (formB n F) = specialSubgroup (formB n F) ⊓
      (spinorNorm (formB n F) (polarB_nondegenerate h2) h2).ker
  even_intrinsic : (2 : F) = 0 → elementarySubgroup (formB n F) = ⊤
  elementary_equals_derived : elementarySubgroup (formB n F) = commutator (O_B n F)
  faithful_rank_ge_two : 2 ≤ n → FaithfulSMul (B n F) (SingularPoints (formB n F))
  odd_transitive_rank_ge_two : 2 ≤ n → (2 : F) ≠ 0 →
    MulAction.IsPretransitive (B n F) (SingularPoints (formB n F))
  odd_elementary_primitive_rank_ge_three : 3 ≤ n → (2 : F) ≠ 0 →
    MulAction.IsPreprimitive (elementarySubgroup (formB n F)) (SingularPoints (formB n F))
  roots_abelian : ∀ p : SingularPoints (formB n F),
    IsMulCommutative (projectiveRootSubgroup (formB n F) p)
  roots_normal_in_stabilizer : ∀ p : SingularPoints (formB n F),
    ((projectiveRootSubgroup (formB n F) p).subgroupOf (MulAction.stabilizer (B n F) p)).Normal
  odd_roots_normal_generate : 2 ≤ n → (2 : F) ≠ 0 → ∀ p : SingularPoints (formB n F),
    Subgroup.normalClosure (projectiveRootSubgroup (formB n F) p : Set (B n F)) = ⊤

theorem typeB_structural_construction {F : Type*} [Field F] [Finite F] (n : ℕ)
    (h : B_good n (Nat.card F)) : TypeBStructuralConstruction n F := by
  exact {
    toTypeBAllRanksConstruction := typeB_all_ranks_construction n h
    numerator_positive := B_order_numerator_positive n _ h.2.1
    denominator_positive := B_order_denominator_positive _
    elementary_order_exact := B_elementary_card_mul_denominator_all_rank n h.1
    elementary_index := B_elementary_index_all_rank n h.1
    center_trivial := B_center_eq_bot_all_rank n h.1
    center_order := B_center_order_all_rank n h.1
    scalar_equals_center := B_scalar_eq_center_all_rank n h.1
    odd_intrinsic := B_odd_intrinsic_all_rank n h.1
    even_intrinsic := B_even_intrinsic n
    elementary_equals_derived := B_elementary_eq_derived_all_rank n h
    faithful_rank_ge_two := B_faithful n
    odd_transitive_rank_ge_two := B_odd_transitive n
    odd_elementary_primitive_rank_ge_three := B_odd_elementary_primitive n
    roots_abelian := B_roots_abelian n
    roots_normal_in_stabilizer := B_roots_normal_in_stabilizer n
    odd_roots_normal_generate := B_odd_roots_normal_generate n }

theorem typeB_prime_power_structural (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (h : B_good n (p ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ TypeBStructuralConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  exact ⟨GaloisField p f,inferInstance,inferInstance,hc,
    typeB_structural_construction n (by simpa only [hc] using h)⟩

/-- The group witness is the public quadratic model itself, with identity comparison. -/
theorem exists_typeB_structural {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : B_good n (Nat.card F)) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = B_order n (Nat.card F) ∧ Nonempty (G ≃* B n F) ∧ TypeBStructuralConstruction n F := by
  have hc := typeB_structural_construction (F := F) n h
  exact ⟨B n F,inferInstance,hc.finite,hc.simple,hc.nonabelian,hc.order,⟨MulEquiv.refl _⟩,hc⟩
end Atlas
