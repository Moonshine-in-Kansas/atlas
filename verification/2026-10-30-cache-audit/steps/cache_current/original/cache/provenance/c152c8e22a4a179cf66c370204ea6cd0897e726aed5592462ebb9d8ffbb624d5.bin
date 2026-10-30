/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.PSLFamily
import Mathlib.FieldTheory.Finite.GaloisField

/-! # The constructed type-A family, with order and projective structure -/

namespace Atlas
open scoped MatrixGroups LinearAlgebra.Projectivization

/-- The verified package concerns the existing PSL construction itself. -/
structure TypeAConstruction (n : ℕ) (F : Type*) [Field F] : Prop where
  finite : Finite (PSL(n, F))
  simple : IsSimpleGroup (PSL(n, F))
  nonabelian : ¬ IsMulCommutative (PSL(n, F))
  order : Nat.card (PSL(n, F)) =
    (Nat.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) /
      Nat.gcd n (Nat.card F - 1)
  order_exact : Nat.card (PSL(n, F)) * (Nat.card F - 1) * Nat.gcd n (Nat.card F - 1) =
    ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ))
  faithful : FaithfulSMul (PSL(n, F)) (ℙ F (Fin n → F))
  doubly_transitive : MulAction.IsMultiplyPretransitive (PSL(n, F)) (ℙ F (Fin n → F)) 2
  primitive : MulAction.IsPreprimitive (PSL(n, F)) (ℙ F (Fin n → F))
  points : Nat.card (ℙ F (Fin n → F)) = (Nat.card F ^ n - 1) / (Nat.card F - 1)
  generated : Subgroup.closure (projectiveElementaryGenerators (ι := Fin n) (F := F)) = ⊤
  embedding_injective :
    Function.Injective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin n) (R := F))
  normal_image : (pslImage (Fin n) F).Normal
  diagonal_quotient : Nonempty ((PGL(n, F) ⧸ pslImage (Fin n) F) ≃* DiagonalQuotient n F)
  diagonal_index : (pslImage (Fin n) F).index = Nat.gcd n (Nat.card F - 1)

theorem typeA_construction {F : Type*} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
    TypeAConstruction n F := by
  let : NeZero n := ⟨by omega⟩
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨hs, ha⟩ := psl_nonabelian_simple (F := F) n hn h2 h3
  exact {
    finite := finite_psl
    simple := hs
    nonabelian := ha
    order := card_psl_factor n
    order_exact := card_psl_mul_factors n
    faithful := psl_faithful
    doubly_transitive := psl_two_pretransitive
    primitive := psl_primitive
    points := card_projectiveSpace n
    generated := psl_elementary_generation
    embedding_injective := psl_toPGL_injective
    normal_image := pslImage_normal
    diagonal_quotient := ⟨by
      have e := pglQuotientPSLEquiv (ι := Fin n) (F := F)
      rw [Fintype.card_fin] at e
      exact e⟩
    diagonal_index := by simpa using (index_pslImage (ι := Fin n) (F := F)) }

/-- Existence with actual group and action witnesses, supplied by constructed PSL. -/
theorem exists_typeA {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
    ∃ (G : Type u) (_ : Group G) (_ : MulAction G (ℙ F (Fin n → F))),
      Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G =
        (Nat.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) /
          Nat.gcd n (Nat.card F - 1) ∧
      FaithfulSMul G (ℙ F (Fin n → F)) ∧
      MulAction.IsMultiplyPretransitive G (ℙ F (Fin n → F)) 2 ∧
      Nonempty (G ≃* PSL(n, F)) ∧ TypeAConstruction n F := by
  have h := typeA_construction (F := F) n hn h2 h3
  exact ⟨PSL(n, F), inferInstance, inferInstance, h.finite, h.simple, h.nonabelian,
    h.order, h.faithful, h.doubly_transitive, ⟨MulEquiv.refl _⟩, h⟩

/-- Numerical prime-power parameters are realized by mathlib's Galois fields. -/
theorem typeA_prime_power (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (h2 : (n, p ^ f) ≠ (2, 2)) (h3 : (n, p ^ f) ≠ (2, 3)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p ^ f ∧ TypeAConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  refine ⟨GaloisField p f, inferInstance, inferInstance, hc, ?_⟩
  apply typeA_construction n hn
  · simpa only [hc] using h2
  · simpa only [hc] using h3

end Atlas
