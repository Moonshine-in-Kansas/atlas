import Atlas.LinearGroups.Symplectic.OrderInterface
import Atlas.LinearGroups.Symplectic.FullLinearIsometries
import Atlas.LinearGroups.Symplectic.Exceptions
import Atlas.LinearGroups.Symplectic.Noncommutative
import Atlas.LinearGroups.Symplectic.ProjectiveEmbedding
import Atlas.LinearGroups.Symplectic.RankOneAction
import Mathlib.FieldTheory.Finite.GaloisField

noncomputable section
namespace Atlas
open Symplectic

/-- The full type-C package concerns the retained matrix group and its actual central quotient.
The rank is n and the natural dimension is 2*n. -/
structure TypeCConstruction (n : ℕ) (F : Type*) [Field F] : Prop where
  positive_rank : 0 < n
  finite_linear : Finite (Sp n F)
  finite : Finite (PSp n F)
  linear_order : Nat.card (Sp n F) = orderNumerator n (Nat.card F)
  center_order : Nat.card (Subgroup.center (Sp n F)) = Nat.gcd 2 (Nat.card F-1)
  denominator_positive : 0 < Nat.gcd 2 (Nat.card F-1)
  order_exact : Nat.gcd 2 (Nat.card F-1) * Nat.card (PSp n F) = orderNumerator n (Nat.card F)
  order_divisibility : Nat.gcd 2 (Nat.card F-1) ∣ orderNumerator n (Nat.card F)
  order : Nat.card (PSp n F) = orderNumerator n (Nat.card F) / Nat.gcd 2 (Nat.card F-1)
  simple : IsSimpleGroup (PSp n F)
  nonabelian : ¬ IsMulCommutative (PSp n F)
  perfect_linear : Group.IsPerfect (Sp n F)
  perfect : Group.IsPerfect (PSp n F)
  quotient_surjective : Function.Surjective (projection (n := n) (F := F))
  quotient_kernel : (projection (n := n) (F := F)).ker = Subgroup.center (Sp n F)
  faithful_linear : FaithfulSMul (Sp n F) (Vector n F)
  faithful : FaithfulSMul (PSp n F) (Points n F)
  transitive : MulAction.IsPretransitive (PSp n F) (Points n F)
  primitive : 2 ≤ n → MulAction.IsPreprimitive (PSp n F) (Points n F)
  points : Nat.card (Points n F) = (Nat.card F^(2*n)-1)/(Nat.card F-1)
  generated_linear : transvectionGroup (n := n) (F := F) = ⊤
  generated : projectiveTransvectionGroup (n := n) (F := F) = ⊤
  line_groups_generate : (⨆ p : Points n F,lineTransvections p) = ⊤
  line_groups_abelian : ∀ p : Points n F, IsMulCommutative (lineTransvections p)
  line_groups_order : ∀ p : Points n F, Nat.card (lineTransvections p) = Nat.card F
  embedding_injective : Function.Injective (toPGL (n := n) (F := F))
  embedding_action : ∀ (g : PSp n F) (p : Points n F), toPGL g • p = g • p
  rank_three : 2 ≤ n → ∀ p x y : Points n F,
    y ∈ MulAction.orbit (MulAction.stabilizer (PSp n F) p) x ↔
      suborbitIndex p x = suborbitIndex p y

theorem typeC_construction {F : Type*} [Field F] [Finite F] (n : ℕ)
    (h : Good n (Nat.card F)) : TypeCConstruction n F := by
  have hn : 0 < n := by rcases h with h|h <;> omega
  exact {
    positive_rank := hn
    finite_linear := inferInstance
    finite := inferInstance
    linear_order := card_sp n F
    center_order := card_center hn
    denominator_positive := Nat.gcd_pos_of_pos_left _ (by decide)
    order_exact := by simpa only [mul_comm] using card_psp_mul_center (F := F) hn
    order_divisibility := center_order_dvd hn
    order := card_psp hn
    simple := simple_of_good h
    nonabelian := projective_not_commutative h
    perfect_linear := perfect_of_good h
    perfect := projective_perfect_of_good h
    quotient_surjective := projection_surjective
    quotient_kernel := projection_kernel
    faithful_linear := inferInstance
    faithful := inferInstance
    transitive := inferInstance
    primitive := projective_preprimitive
    points := card_points
    generated_linear := transvectionGroup_eq_top
    generated := projectiveTransvectionGroup_eq_top
    line_groups_generate := Symplectic.lineTransvections_generate
    line_groups_abelian := Symplectic.lineTransvections_abelian
    line_groups_order := card_lineTransvections
    embedding_injective := toPGL_injective
    embedding_action := toPGL_action
    rank_three := stabilizer_orbit_iff }

/-- Existence is witnessed by the constructed matrix central quotient itself. -/
theorem exists_typeC {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : Good n (Nat.card F)) :
    ∃ (G : Type u) (_ : Group G) (_ : MulAction G (Points n F)),
      Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = orderNumerator n (Nat.card F) / Nat.gcd 2 (Nat.card F-1) ∧
      FaithfulSMul G (Points n F) ∧ Nonempty (G ≃* PSp n F) ∧ TypeCConstruction n F := by
  have hc := typeC_construction n h
  exact ⟨PSp n F,inferInstance,inferInstance,hc.finite,hc.simple,hc.nonabelian,
    hc.order,hc.faithful,⟨MulEquiv.refl _⟩,hc⟩

/-- Every allowed prime-power parameter is realized by an actual finite field. -/
theorem typeC_prime_power (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (h : Good n (p^f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p^f ∧ TypeCConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  refine ⟨GaloisField p f,inferInstance,inferInstance,hc,typeC_construction n ?_⟩
  simpa only [hc] using h

end Atlas
