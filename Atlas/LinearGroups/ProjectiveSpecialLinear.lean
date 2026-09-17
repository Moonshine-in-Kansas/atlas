/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.ProjectiveGeneralLinear
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain

/-!
# Finite projective special linear groups

The scalar center is counted through the power map on the cyclic group of field
units. Determinant modulo powers identifies the diagonal quotient PGL/PSL.
-/

namespace Atlas

open scoped MatrixGroups LinearAlgebra.Projectivization

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- The center of SL consists of scalar matrices with determinant one. -/
theorem sl_mem_center_iff (g : Matrix.SpecialLinearGroup ι F) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup ι F) ↔
      ∃ a : F, a ^ Fintype.card ι = 1 ∧ Matrix.scalar ι a = g :=
  Matrix.SpecialLinearGroup.mem_center_iff

/-- Equivalently, the central scalars are the units whose nth power is one. -/
theorem sl_mem_center_iff_units (g : Matrix.SpecialLinearGroup ι F) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup ι F) ↔
      ∃ a : Fˣ, a ^ Fintype.card ι = 1 ∧
        Matrix.GeneralLinearGroup.scalar ι a = Matrix.SpecialLinearGroup.toGL g := by
  rw [← Matrix.SpecialLinearGroup.toGL_mem_center_iff,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ha⟩
    simpa using congrArg Matrix.GeneralLinearGroup.det ha
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩

/-- The scalar center is identified with the kernel of the power map on units. -/
noncomputable def slCenterEquivPowerKernel [Nonempty ι] :
    Subgroup.center (Matrix.SpecialLinearGroup ι F) ≃*
      (powMonoidHom (Fintype.card ι) : Fˣ →* Fˣ).ker :=
  (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (Classical.arbitrary ι)).trans
    (MulEquiv.subgroupCongr rootsOfUnity_eq_ker)

/-- The center of SL has the expected gcd order. -/
theorem card_sl_center [Nonempty ι] [Finite F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup ι F)) =
      Nat.gcd (Fintype.card ι) (Nat.card F - 1) := by
  rw [Nat.card_congr (slCenterEquivPowerKernel (ι := ι) (F := F)).toEquiv,
    IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_comm]

/-- The determinant target for the diagonal quotient. -/
abbrev DiagonalQuotient (n : ℕ) (F : Type*) [Field F] :=
  Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range

/-- The existing canonical PSL subgroup of PGL. -/
abbrev pslImage (ι F : Type*) [Fintype ι] [DecidableEq ι] [Field F] :
    Subgroup (PGL(ι, F)) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := ι) (R := F)).range

/-- The canonical homomorphism PSL → PGL is injective. -/
theorem psl_toPGL_injective :
    Function.Injective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := ι) (R := F)) :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

/-- Determinant modulo nth powers is unchanged by scalar multiplication. -/
def pglDet : PGL(ι, F) →* DiagonalQuotient (Fintype.card ι) F :=
  Matrix.ProjGenLinGroup.lift
    ((QuotientGroup.mk' _).comp Matrix.GeneralLinearGroup.det) (by
      ext u
      change QuotientGroup.mk (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar ι u)) = 1
      rw [Matrix.GeneralLinearGroup.det_scalar, QuotientGroup.eq_one_iff]
      exact ⟨u, rfl⟩)

/-- The quotient determinant is represented by the determinant of any lift. -/
@[simp] theorem pglDet_mk (g : GL ι F) :
    pglDet (Matrix.ProjGenLinGroup.mk g) = QuotientGroup.mk g.det := rfl

/-- Every determinant class occurs in positive dimension. -/
theorem pglDet_surjective [Nonempty ι] :
    Function.Surjective (pglDet (ι := ι) (F := F)) := by
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.det_surjective (n := ι) u
  exact ⟨Matrix.ProjGenLinGroup.mk g, rfl⟩

/-- The image of PSL is exactly the kernel of determinant modulo powers. -/
theorem pglDet_ker : (pglDet (ι := ι) (F := F)).ker = pslImage ι F := by
  ext x
  induction x using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    constructor
    · intro hg
      have hd : g.det ∈ (powMonoidHom (Fintype.card ι) : Fˣ →* Fˣ).range :=
        (QuotientGroup.eq_one_iff g.det).mp hg
      obtain ⟨u, hu⟩ := hd
      let g' := g * Matrix.GeneralLinearGroup.scalar ι u⁻¹
      have hd' : g'.det = 1 := by
        simp [g', ← hu]
      let s : Matrix.SpecialLinearGroup ι F := ⟨g'.val, congrArg Units.val hd'⟩
      have hs : Matrix.SpecialLinearGroup.toGL s = g' := Units.ext rfl
      refine ⟨QuotientGroup.mk s, ?_⟩
      rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hs]
      simp [g']
    · rintro ⟨s, hs⟩
      rw [← hs]
      induction s using QuotientGroup.induction_on with
      | H s =>
        change pglDet (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s)) = 1
        simp

/-- The canonical PSL image is normal in PGL. -/
instance pslImage_normal : (pslImage ι F).Normal := by
  rw [← pglDet_ker]
  infer_instance

/-- The full determinant-induced isomorphism PGL/PSL ≃ F×/(F×)^n. -/
noncomputable def pglQuotientPSLEquiv [Nonempty ι] :
    (PGL(ι, F) ⧸ pslImage ι F) ≃* DiagonalQuotient (Fintype.card ι) F :=
  (QuotientGroup.quotientMulEquivOfEq pglDet_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective pglDet pglDet_surjective)

/-- The quotient isomorphism is the natural map induced by determinant. -/
@[simp] theorem pglQuotientPSLEquiv_mk [Nonempty ι] (g : GL ι F) :
    pglQuotientPSLEquiv (QuotientGroup.mk (Matrix.ProjGenLinGroup.mk g)) =
      QuotientGroup.mk g.det := rfl

/-- The index is obtained from the power-map quotient of the cyclic unit group. -/
theorem index_pslImage [Nonempty ι] [Finite F] :
    (pslImage ι F).index = Nat.gcd (Fintype.card ι) (Nat.card F - 1) := by
  rw [Subgroup.index_eq_card,
    Nat.card_congr (pglQuotientPSLEquiv (ι := ι) (F := F)).toEquiv,
    ← Subgroup.index_eq_card, IsCyclic.index_powMonoidHom_range,
    Nat.card_units, Nat.gcd_comm]

/-- PSL is finite over every finite field. -/
theorem finite_psl [Finite F] : Finite (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  inferInstance

/-- The embedded copy of PSL has the same cardinality as PSL. -/
theorem card_pslImage :
    Nat.card (pslImage ι F) = Nat.card (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  (Nat.card_congr (MonoidHom.ofInjective
    (psl_toPGL_injective (ι := ι) (F := F))).toEquiv).symm

/-- The exact integer order identity coming from the diagonal quotient. -/
theorem card_psl_mul_pgl [Nonempty ι] [Finite F] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup ι F) *
      Nat.gcd (Fintype.card ι) (Nat.card F - 1) = Nat.card (PGL(ι, F)) := by
  rw [← card_pslImage, ← index_pslImage]
  exact Subgroup.card_mul_index _

/-- The diagonal index divides the order of PGL. -/
theorem diagonal_index_dvd_pgl [Nonempty ι] [Finite F] :
    Nat.gcd (Fintype.card ι) (Nat.card F - 1) ∣ Nat.card (PGL(ι, F)) := by
  rw [← index_pslImage (ι := ι)]
  exact Subgroup.index_dvd_card _

/-- The order of PSL expressed using the order of PGL. -/
theorem card_psl [Nonempty ι] [Finite F] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup ι F) =
      Nat.card (PGL(ι, F)) / Nat.gcd (Fintype.card ι) (Nat.card F - 1) := by
  rw [← card_psl_mul_pgl (ι := ι), Nat.mul_div_cancel]
  exact Nat.gcd_pos_of_pos_left _ Fintype.card_pos

/-- The central quotient formula starting directly from SL. -/
theorem card_psl_from_sl [Nonempty ι] [Finite F] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup ι F) =
      Nat.card (Matrix.SpecialLinearGroup ι F) /
        Nat.gcd (Fintype.card ι) (Nat.card F - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup ι F)), card_sl_center,
    Nat.mul_div_cancel]
  exact Nat.gcd_pos_of_pos_left _ Fintype.card_pos

/-- The textbook ordered-basis formula for PSL over an arbitrary finite field. -/
theorem card_psl_product (n : ℕ) [NeZero n] [Finite F] :
    Nat.card (PSL(n, F)) =
      (∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ))) /
        ((Nat.card F - 1) * Nat.gcd n (Nat.card F - 1)) := by
  rw [card_psl, card_pgl_product, Fintype.card_fin, Nat.div_div_eq_div_mul]

/-- The equivalent factored formula, with the entire numerator divided exactly. -/
theorem card_psl_factor (n : ℕ) [NeZero n] [Finite F] :
    Nat.card (PSL(n, F)) =
      (Nat.card F ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) /
          Nat.gcd n (Nat.card F - 1) := by
  rw [card_psl, card_pgl_factor, Fintype.card_fin]

/-- The fraction-free standard order identity. -/
theorem card_psl_mul_factors (n : ℕ) [NeZero n] [Finite F] :
    Nat.card (PSL(n, F)) * (Nat.card F - 1) * Nat.gcd n (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  have h := card_psl_mul_pgl (ι := Fin n) (F := F)
  simp only [Fintype.card_fin] at h
  calc
    _ = (Nat.card (PSL(n, F)) * Nat.gcd n (Nat.card F - 1)) * (Nat.card F - 1) := by
      ac_rfl
    _ = Nat.card (PGL(n, F)) * (Nat.card F - 1) := by rw [h]
    _ = _ := by rw [card_pgl_mul, card_gl]

/-- The action of PSL on projective points is the faithful action from mathlib. -/
theorem psl_faithful :
    FaithfulSMul (Matrix.ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) :=
  inferInstance

/-- Double transitivity descends from SL, with no small-field exceptions. -/
instance psl_two_pretransitive :
    MulAction.IsMultiplyPretransitive
      (Matrix.ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) 2 := by
  let f : (ℙ F (ι → F)) →ₑ[QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup ι F))] (ℙ F (ι → F)) :=
    { toFun := id
      map_smul' _ _ := rfl }
  exact MulAction.IsPretransitive.of_embedding (f := f) Function.surjective_id

/-- Transitivity of the natural PSL action. -/
instance psl_pretransitive :
    MulAction.IsPretransitive (Matrix.ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) :=
  MulAction.isPretransitive_of_is_two_pretransitive

/-- Primitivity of the natural PSL action, reused from mathlib. -/
theorem psl_primitive :
    MulAction.IsPreprimitive (Matrix.ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) :=
  inferInstance

/-- The embedding into PGL respects the natural projective actions. -/
theorem psl_toPGL_smul (g : Matrix.ProjectiveSpecialLinearGroup ι F) (p : ℙ F (ι → F)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL g • p = g • p := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction p using Projectivization.ind with
    | _ v hv => rfl

end Atlas
