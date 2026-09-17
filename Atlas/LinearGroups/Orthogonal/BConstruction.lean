import Atlas.LinearGroups.Orthogonal.BFamily
import Atlas.LinearGroups.Orthogonal.SimplicityCompleteB
import Atlas.LinearGroups.Orthogonal.ProjectiveFieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Public rank-at-least-two B construction with the exact exception

The carrier remains the scalar quotient of the actual elementary quadratic
isometry subgroup. Rank-one comparison is a separate construction checkpoint.
-/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem B_simple_iff (n : ℕ) (hn : 2 ≤ n) :
    IsSimpleGroup (B n F) ↔ (n, Nat.card F) ≠ (2, 2) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveB_simple_iff k

theorem B_simple (n : ℕ) (hn : 2 ≤ n) (h : (n, Nat.card F) ≠ (2, 2)) :
    IsSimpleGroup (B n F) := (B_simple_iff n hn).mpr h

theorem B_noncommutative (n : ℕ) (hn : 2 ≤ n) (h : (n, Nat.card F) ≠ (2, 2)) :
    ¬ IsMulCommutative (B n F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveB_noncommutative k h

theorem B_elementary_perfect (n : ℕ) (hn : 2 ≤ n) (h : (n, Nat.card F) ≠ (2, 2)) :
    Group.IsPerfect (elementarySubgroup (formB n F)) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    letI := even_full_perfect (F := F) (Or.inr ⟨hn,h⟩)
    exact Group.IsPerfect.ofSurjective (f := evenElementaryBEquivFull.symm.toMonoidHom)
      evenElementaryBEquivFull.symm.surjective
  · obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
    cases k with
    | zero => exact elementaryB_two_perfect h2
    | succ k => exact elementaryB_perfect_stable k h2

theorem B_perfect (n : ℕ) (hn : 2 ≤ n) (h : (n, Nat.card F) ≠ (2, 2)) :
    Group.IsPerfect (B n F) := by
  letI := B_elementary_perfect n hn h
  exact projectiveElementary_perfect _

theorem B_scalar_eq_bot (n : ℕ) (hn : 2 ≤ n) : elementaryScalarSubgroup (formB n F) = ⊥ := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact even_elementaryScalar_eq_bot _
  · obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
    exact bot_unique ((elementaryScalarSubgroup_le_center _).trans_eq (elementaryB_center_eq_bot k h2))

def B_elementaryEquiv (n : ℕ) (hn : 2 ≤ n) : B n F ≃* elementarySubgroup (formB n F) :=
  (QuotientGroup.quotientMulEquivOfEq (B_scalar_eq_bot n hn)).trans QuotientGroup.quotientBot

theorem B_center_eq_bot (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.center (elementarySubgroup (formB n F)) = ⊥ := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    let e := (evenElementaryBEquivFull (n := n) (F := F)).trans evenFullEquivSp
    apply bot_unique
    intro g hg
    have hm : e g ∈ Subgroup.center (Atlas.Symplectic.Sp n F) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨g,hg,rfl⟩
    rw [even_symplectic_center (by omega),Subgroup.mem_bot] at hm
    exact e.injective (hm.trans e.map_one.symm)
  · obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
    exact elementaryB_center_eq_bot k h2

theorem B_elementary_order (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (elementarySubgroup (formB n F)) = B_order n (Nat.card F) := by
  rw [← Nat.card_congr (B_elementaryEquiv (F := F) n hn).toEquiv]
  exact B_card n hn

theorem B_odd_intrinsic (n : ℕ) (hn : 2 ≤ n) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB n F) = specialSubgroup (formB n F) ⊓
      (spinorNorm (formB n F) (polarB_nondegenerate h2) h2).ker := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact elementaryB_eq_intrinsicKernel k h2

theorem B_even_intrinsic (n : ℕ) (h2 : (2 : F) = 0) :
    elementarySubgroup (formB n F) = ⊤ := by
  letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  exact even_elementary_eq_top

theorem B_generated_by_siegel (n : ℕ) :
    elementarySubgroup (formB n F) = Subgroup.closure
      {g | ∃ u v hu huv, g = siegelElement (formB n F) u v hu huv} := rfl

variable {K : Type*} [Field K]
def B_fieldEquiv (n : ℕ) (e : F ≃+* K) : B n F ≃* B n K := fieldEquivProjectiveElementaryB e
omit [Finite F] in
theorem B_fieldEquiv_projection (n : ℕ) (e : F ≃+* K)
    (g : elementarySubgroup (formB n F)) :
    B_fieldEquiv n e (projectiveElementaryMap _ g) =
      projectiveElementaryMap _ (fieldEquivElementaryB e g) := rfl
end Atlas.Orthogonal

namespace Atlas
open Orthogonal
universe u
structure TypeBConstruction (n : ℕ) (F : Type*) [Field F] : Prop where
  rank_bound : 2 ≤ n
  finite_full : Finite (O_B n F)
  finite_elementary : Finite (elementarySubgroup (formB n F))
  finite : Finite (B n F)
  full_order : Nat.card (O_B n F) =
    (if (2 : F) = 0 then 1 else 2) * B_order_numerator n (Nat.card F)
  elementary_order : Nat.card (elementarySubgroup (formB n F)) = B_order n (Nat.card F)
  scalar_trivial : elementaryScalarSubgroup (formB n F) = ⊥
  center_trivial : Subgroup.center (elementarySubgroup (formB n F)) = ⊥
  odd_intrinsic : ∀ h2 : (2 : F) ≠ 0,
    elementarySubgroup (formB n F) = specialSubgroup (formB n F) ⊓
      (spinorNorm (formB n F) (polarB_nondegenerate h2) h2).ker
  even_intrinsic : (2 : F) = 0 → elementarySubgroup (formB n F) = ⊤
  denominator_positive : 0 < B_order_denominator (Nat.card F)
  numerator_positive : 0 < B_order_numerator n (Nat.card F)
  order_exact : Nat.card (B n F) * B_order_denominator (Nat.card F) = B_order_numerator n (Nat.card F)
  order_divisibility : B_order_denominator (Nat.card F) ∣ B_order_numerator n (Nat.card F)
  order : Nat.card (B n F) = B_order n (Nat.card F)
  simple_iff : IsSimpleGroup (B n F) ↔ (n, Nat.card F) ≠ (2, 2)
  simple : IsSimpleGroup (B n F)
  nonabelian : ¬ IsMulCommutative (B n F)
  perfect_elementary : Group.IsPerfect (elementarySubgroup (formB n F))
  perfect : Group.IsPerfect (B n F)
  quotient_surjective : Function.Surjective (projectiveElementaryMap (formB n F))
  quotient_kernel : (projectiveElementaryMap (formB n F)).ker = elementaryScalarSubgroup (formB n F)
  generation : elementarySubgroup (formB n F) = Subgroup.closure
    {g | ∃ u v hu huv, g = siegelElement (formB n F) u v hu huv}

theorem typeB_construction {F : Type*} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h : (n, Nat.card F) ≠ (2, 2)) : TypeBConstruction n F := by
  have hq : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  exact {
    rank_bound := hn
    finite_full := inferInstance
    finite_elementary := inferInstance
    finite := B_finite n
    full_order := by simpa only [B_order_numerator,mul_assoc] using card_fullB (F := F) n
    elementary_order := B_elementary_order n hn
    scalar_trivial := B_scalar_eq_bot n hn
    center_trivial := B_center_eq_bot n hn
    odd_intrinsic := B_odd_intrinsic n hn
    even_intrinsic := B_even_intrinsic n
    denominator_positive := B_order_denominator_positive _
    numerator_positive := B_order_numerator_positive n _ hq
    order_exact := B_card_mul_denominator n hn
    order_divisibility := B_order_divisibility n hn
    order := B_card n hn
    simple_iff := B_simple_iff n hn
    simple := B_simple n hn h
    nonabelian := B_noncommutative n hn h
    perfect_elementary := B_elementary_perfect n hn h
    perfect := B_perfect n hn h
    quotient_surjective := projectiveElementaryMap_surjective _
    quotient_kernel := projectiveElementaryMap_kernel _
    generation := B_generated_by_siegel n }

theorem exists_typeB {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h : (n, Nat.card F) ≠ (2, 2)) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = B_order n (Nat.card F) ∧ Nonempty (G ≃* B n F) ∧ TypeBConstruction n F := by
  have hc := typeB_construction (F := F) n hn h
  exact ⟨B n F,inferInstance,hc.finite,hc.simple,hc.nonabelian,hc.order,⟨MulEquiv.refl _⟩,hc⟩

theorem typeB_prime_power (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (h : (n, p ^ f) ≠ (2, 2)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ TypeBConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  exact ⟨GaloisField p f,inferInstance,inferInstance,hc,typeB_construction n hn (by simpa only [hc] using h)⟩
end Atlas
