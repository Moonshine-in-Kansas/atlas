import Atlas.LinearGroups.Orthogonal.BAllRanks
import Atlas.LinearGroups.Orthogonal.BConstruction
import Atlas.LinearGroups.PSLFamily

/-! # The actual B family in all positive ranks, with all three exact exceptions

This public theorem package retains the quadratic-form model and its actual
scalar quotient. Low-rank comparisons are used through their proved maps.
-/
noncomputable section
open scoped MatrixGroups Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem B_simple_iff_all_rank (n : ℕ) (hn : 1 ≤ n) :
    IsSimpleGroup (B n F) ↔ (n, Nat.card F) ≠ (1, 2) ∧
      (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2) := by
  by_cases h : n = 1
  · subst n
    have he : IsSimpleGroup (B 1 F) ↔ IsSimpleGroup (PSL(2,F)) := by
      constructor
      · intro hs
        letI := hs
        exact B1Conjugation.projectiveEquivPSL.symm.isSimpleGroup
      · intro hs
        letI := hs
        exact B1Conjugation.projectiveEquivPSL.isSimpleGroup
    rw [he,Atlas.psl_simple_iff 2 (by decide)]
    simp
  · rw [B_simple_iff n (by omega)]
    have hn1 : n ≠ 1 := h
    simp [Prod.ext_iff,hn1]

theorem B_simple_all_rank (n : ℕ) (h : B_good n (Nat.card F)) : IsSimpleGroup (B n F) :=
  (B_simple_iff_all_rank n h.1).mpr h.2.2

theorem B_elementary_perfect_all_rank (n : ℕ) (h : B_good n (Nat.card F)) :
    Group.IsPerfect (elementarySubgroup (formB n F)) := by
  by_cases hn : n = 1
  · subst n
    have hq : 4 ≤ Nat.card F := by
      have h2 : Nat.card F ≠ 2 := by simpa using h.2.2.1
      have h3 : Nat.card F ≠ 3 := by simpa using h.2.2.2.1
      have := h.2.1
      omega
    obtain ⟨a,ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) (k := 2) (by decide)
      (by rw [Nat.card_units]; omega)
    have ha' : (a : F) ^ 2 ≠ 1 := fun hh => ha (Units.ext (by simpa using hh))
    letI : Group.IsPerfect (SL(2,F)) := ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero a) ha'⟩
    exact Group.IsPerfect.ofSurjective (f := B1Conjugation.toElementary)
      B1Conjugation.toElementary_surjective
  · exact B_elementary_perfect n (by have := h.1; omega) h.2.2.2.2

theorem B_perfect_all_rank (n : ℕ) (h : B_good n (Nat.card F)) : Group.IsPerfect (B n F) := by
  letI := B_elementary_perfect_all_rank n h
  exact projectiveElementary_perfect _

theorem B_noncommutative_all_rank (n : ℕ) (h : B_good n (Nat.card F)) :
    ¬ IsMulCommutative (B n F) := by
  by_cases hn : n = 1
  · subst n
    have hq : 4 ≤ Nat.card F := by
      have h2 : Nat.card F ≠ 2 := by simpa using h.2.2.1
      have h3 : Nat.card F ≠ 3 := by simpa using h.2.2.2.1
      have := h.2.1
      omega
    intro hc
    exact Atlas.psl_nonabelian_rank_two hq
      (Function.Surjective.isMulCommutative B1Conjugation.projectiveEquivPSL.surjective hc)
  · exact B_noncommutative n (by have := h.1; omega) h.2.2.2.2

theorem B_scalar_eq_bot_all_rank (n : ℕ) (hn : 1 ≤ n) :
    elementaryScalarSubgroup (formB n F) = ⊥ := by
  by_cases h : n = 1
  · subst n
    exact B1Conjugation.elementaryScalar_eq_bot
  · exact B_scalar_eq_bot n (by omega)

def B_elementaryEquiv_all_rank (n : ℕ) (hn : 1 ≤ n) :
    B n F ≃* elementarySubgroup (formB n F) :=
  (QuotientGroup.quotientMulEquivOfEq (B_scalar_eq_bot_all_rank n hn)).trans QuotientGroup.quotientBot

theorem B_elementary_order_all_rank (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (elementarySubgroup (formB n F)) = B_order n (Nat.card F) := by
  rw [← Nat.card_congr (B_elementaryEquiv_all_rank (F := F) n hn).toEquiv]
  exact B_card_all_rank n hn
end Atlas.Orthogonal

namespace Atlas
open Orthogonal
universe u
/-- Uniform order and simplicity package on the actual quadratic model. The
separate intrinsic and geometric interfaces retain their explicitly stated scopes. -/
structure TypeBAllRanksConstruction (n : ℕ) (F : Type*) [Field F] : Prop where
  admissible : B_good n (Nat.card F)
  finite_full : Finite (O_B n F)
  finite_elementary : Finite (elementarySubgroup (formB n F))
  finite : Finite (B n F)
  full_order : Nat.card (O_B n F) =
    (if (2 : F) = 0 then 1 else 2) * B_order_numerator n (Nat.card F)
  elementary_order : Nat.card (elementarySubgroup (formB n F)) = B_order n (Nat.card F)
  scalar_trivial : elementaryScalarSubgroup (formB n F) = ⊥
  order_exact : Nat.card (B n F) * B_order_denominator (Nat.card F) = B_order_numerator n (Nat.card F)
  order_divisibility : B_order_denominator (Nat.card F) ∣ B_order_numerator n (Nat.card F)
  order : Nat.card (B n F) = B_order n (Nat.card F)
  simple_iff : IsSimpleGroup (B n F) ↔ (n, Nat.card F) ≠ (1, 2) ∧
    (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2)
  simple : IsSimpleGroup (B n F)
  nonabelian : ¬ IsMulCommutative (B n F)
  perfect_elementary : Group.IsPerfect (elementarySubgroup (formB n F))
  perfect : Group.IsPerfect (B n F)
  quotient_surjective : Function.Surjective (projectiveElementaryMap (formB n F))
  quotient_kernel : (projectiveElementaryMap (formB n F)).ker = elementaryScalarSubgroup (formB n F)

theorem typeB_all_ranks_construction {F : Type*} [Field F] [Finite F] (n : ℕ)
    (h : B_good n (Nat.card F)) : TypeBAllRanksConstruction n F := by
  exact {
    admissible := h
    finite_full := inferInstance
    finite_elementary := inferInstance
    finite := B_finite n
    full_order := by simpa only [B_order_numerator,mul_assoc] using card_fullB (F := F) n
    elementary_order := B_elementary_order_all_rank n h.1
    scalar_trivial := B_scalar_eq_bot_all_rank n h.1
    order_exact := B_card_mul_denominator_all_rank n h.1
    order_divisibility := B_order_divisibility_all_rank n h.1
    order := B_card_all_rank n h.1
    simple_iff := B_simple_iff_all_rank n h.1
    simple := B_simple_all_rank n h
    nonabelian := B_noncommutative_all_rank n h
    perfect_elementary := B_elementary_perfect_all_rank n h
    perfect := B_perfect_all_rank n h
    quotient_surjective := projectiveElementaryMap_surjective _
    quotient_kernel := projectiveElementaryMap_kernel _ }

theorem exists_typeB_all_ranks {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : B_good n (Nat.card F)) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = B_order n (Nat.card F) ∧ Nonempty (G ≃* B n F) ∧ TypeBAllRanksConstruction n F := by
  have hc := typeB_all_ranks_construction (F := F) n h
  exact ⟨B n F,inferInstance,hc.finite,hc.simple,hc.nonabelian,hc.order,⟨MulEquiv.refl _⟩,hc⟩

theorem typeB_prime_power_all_ranks (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (h : B_good n (p ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ TypeBAllRanksConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  exact ⟨GaloisField p f,inferInstance,inferInstance,hc,
    typeB_all_ranks_construction n (by simpa only [hc] using h)⟩
end Atlas
