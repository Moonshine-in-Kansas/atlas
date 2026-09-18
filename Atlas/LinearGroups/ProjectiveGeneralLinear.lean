/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.GroupTheory.Coset.Card
import Atlas.LinearGroups.OrderArithmetic

/-!
# Finite projective general linear groups

The constructions, scalar-center theorem, and count of invertible matrices are
reused from mathlib. This file packages their finite cardinality consequences.
-/

namespace Atlas

open scoped MatrixGroups LinearAlgebra.Projectivization

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- The center consists exactly of invertible scalar matrices. -/
theorem gl_center_eq_scalars :
    Subgroup.center (GL ι F) = (Matrix.GeneralLinearGroup.scalar ι).range :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar

/-- Scalars embed in GL whenever the vector space has positive dimension. -/
theorem gl_scalar_injective [Nonempty ι] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Fˣ → GL ι F) := by
  intro a b h
  apply Units.ext
  exact Matrix.scalar_inj.mp (congrArg Units.val h)

/-- The scalar center has order q − 1. -/
theorem card_gl_center [Nonempty ι] [Finite F] :
    Nat.card (Subgroup.center (GL ι F)) = Nat.card F - 1 := by
  rw [gl_center_eq_scalars,
    ← Nat.card_congr (MonoidHom.ofInjective (gl_scalar_injective (ι := ι) (F := F))).toEquiv,
    Nat.card_units]

instance finite_pgl [Finite F] : Finite (PGL(ι, F)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The exact integer form of the central quotient order formula. -/
theorem card_pgl_mul [Nonempty ι] [Finite F] :
    Nat.card (PGL(ι, F)) * (Nat.card F - 1) = Nat.card (GL ι F) := by
  rw [← card_gl_center (ι := ι)]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (GL ι F))).symm

/-- The central quotient order formula, with exact natural-number division. -/
theorem card_pgl [Nonempty ι] [Finite F] :
    Nat.card (PGL(ι, F)) = Nat.card (GL ι F) / (Nat.card F - 1) := by
  rw [← card_pgl_mul (ι := ι), Nat.mul_div_cancel]
  exact Nat.sub_pos_of_lt Finite.one_lt_card

/-- The scalar-center order divides the order of GL. -/
theorem scalar_order_dvd_gl [Nonempty ι] [Finite F] :
    Nat.card F - 1 ∣ Nat.card (GL ι F) :=
  ⟨Nat.card (PGL(ι, F)), by rw [← card_pgl_mul (ι := ι), Nat.mul_comm]⟩

/-- The standard GL order formula over every finite field. -/
theorem card_gl (n : ℕ) [Finite F] :
    Nat.card (GL (Fin n) F) = ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  let := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card] using Matrix.card_GL_field (𝔽 := F) n

/-- The standard PGL order formula over every finite field, in positive dimension. -/
theorem card_pgl_product (n : ℕ) [NeZero n] [Finite F] :
    Nat.card (PGL(n, F)) =
      (∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ))) / (Nat.card F - 1) := by
  rw [card_pgl, card_gl]

/-- The equivalent factored GL order formula. -/
theorem card_gl_factor (n : ℕ) [Finite F] :
    Nat.card (GL (Fin n) F) = Nat.card F ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.range n, (Nat.card F ^ (i + 1) - 1) := by
  rw [card_gl, linear_order_product_factor]

/-- The conventional division-free PGL order formula. -/
theorem card_pgl_factor (n : ℕ) [NeZero n] [Finite F] :
    Nat.card (PGL(n, F)) = Nat.card F ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1) := by
  apply Nat.mul_right_cancel (m := Nat.card F - 1)
    (Nat.sub_pos_of_lt Finite.one_lt_card)
  rw [card_pgl_mul, card_gl_factor, linear_order_product_split _ _ (NeZero.pos n)]
  ac_rfl

/-- Projective points counted as nonzero vectors modulo nonzero scalars. -/
theorem card_projectiveSpace (n : ℕ) [Finite F] :
    Nat.card (ℙ F (Fin n → F)) = (Nat.card F ^ n - 1) / (Nat.card F - 1) := by
  simpa [Nat.card_fun] using Projectivization.card'' F (Fin n → F)

/-- The equivalent geometric-sum formula for projective points. -/
theorem card_projectiveSpace_sum (n : ℕ) [Finite F] :
    Nat.card (ℙ F (Fin n → F)) = ∑ i ∈ Finset.range n, Nat.card F ^ i :=
  Projectivization.card_of_finrank F (Fin n → F) (by simp)

/-- Double transitivity descends from the natural SL action. -/
instance pgl_two_pretransitive :
    MulAction.IsMultiplyPretransitive (PGL(ι, F)) (ℙ F (ι → F)) 2 := by
  let f : (ℙ F (ι → F)) →ₑ[Matrix.SpecialLinearGroup.toPGL (n := ι) (R := F)]
      (ℙ F (ι → F)) :=
    { toFun := id
      map_smul' g p := by
        induction p using Projectivization.ind with
        | _ v hv =>
          simp only [id_eq, Projectivization.smul_mk]
          rfl }
  exact MulAction.IsPretransitive.of_embedding (f := f) Function.surjective_id

/-- In particular, PGL acts transitively on projective points. -/
instance pgl_pretransitive : MulAction.IsPretransitive (PGL(ι, F)) (ℙ F (ι → F)) :=
  MulAction.isPretransitive_of_is_two_pretransitive

/-- A linear transformation fixing every projective point is scalar. -/
theorem gl_mem_center_of_fixes_projectiveSpace (g : GL ι F)
    (hg : ∀ p : ℙ F (ι → F), g • p = p) :
    g ∈ Subgroup.center (GL ι F) := by
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  let f : (ι → F) →ₗ[F] (ι → F) := Matrix.mulVecLin g.val
  obtain ⟨a, ha⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent fun v ↦ by
    by_cases hv : v = 0
    · simp [hv, linearIndependent_fin2]
    · simpa [LinearIndependent.pair_iff' hv, Projectivization.smul_mk,
        Projectivization.mk_eq_mk_iff', f] using! hg (.mk F v hv)
  refine ⟨a, ?_⟩
  have h := congrArg LinearMap.toMatrix' ha
  simpa [f, ← Matrix.toLin'_apply', LinearMap.toMatrix'_algebraMap,
    Matrix.smul_one_eq_diagonal] using h.symm

/-- The central quotient acts faithfully on projective points. -/
instance pgl_faithful : FaithfulSMul (PGL(ι, F)) (ℙ F (ι → F)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    apply gl_mem_center_of_fixes_projectiveSpace g
    exact hg

end Atlas
