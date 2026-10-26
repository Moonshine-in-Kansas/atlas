import Atlas.Rudvalis.ProjectiveMatrixFiltration
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Atlas.Tits
open Atlas.Rudvalis

/-- The two constraints saying that M preserves the reference line <(0,1,1)>. -/
def pointMatrixConstraints : BinaryMatrix →ₗ[Bit] (Fin 2 → Bit) where
  toFun M := ![M 0 1 + M 0 2, M 1 1 + M 1 2 + M 2 1 + M 2 2]
  map_add' := by intro M N; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a M; ext i; fin_cases i <;> simp <;> ring

noncomputable def pointMatrixSpace : Submodule Bit BinaryMatrix := pointMatrixConstraints.ker

theorem pointMatrixConstraints_surjective : Function.Surjective pointMatrixConstraints := by
  intro v
  refine ⟨!![0, v 0, 0; 0, v 1, 0; 0, 0, 0], ?_⟩
  ext i
  fin_cases i <;> simp [pointMatrixConstraints]

theorem pointMatrixSpace_finrank : Module.finrank Bit pointMatrixSpace = 7 := by
  have h := pointMatrixConstraints.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr pointMatrixConstraints_surjective] at h
  have hd : Module.finrank Bit BinaryMatrix = 9 := by simp [BinaryMatrix, Module.finrank_matrix]
  have hr : Module.finrank Bit (⊤ : Submodule Bit (Fin 2 → Bit)) = 2 := by simp
  rw [hr, hd] at h
  change 2 + Module.finrank Bit pointMatrixSpace = 9 at h
  omega

noncomputable def pointIdentity : pointMatrixSpace := ⟨1, by
  change pointMatrixConstraints 1 = 0
  decide +kernel⟩

noncomputable def pointScalarLine : Submodule Bit pointMatrixSpace :=
  Submodule.span Bit {pointIdentity}

noncomputable abbrev PointTranslationSpace := pointMatrixSpace ⧸ pointScalarLine

theorem pointScalarLine_finrank : Module.finrank Bit pointScalarLine = 1 := by
  apply finrank_span_singleton
  intro h
  have hc := congrArg (fun M : pointMatrixSpace => M.val 0 0) h
  norm_num [pointIdentity] at hc

theorem pointTranslationSpace_finrank : Module.finrank Bit PointTranslationSpace = 6 := by
  have h := pointScalarLine.finrank_quotient_add_finrank
  rw [pointScalarLine_finrank, pointMatrixSpace_finrank] at h
  change Module.finrank Bit PointTranslationSpace + 1 = 7 at h
  omega

/-- Trace on the quotient by the reference line, written in the inherited coordinates. -/
def pointTraceRaw : BinaryMatrix →ₗ[Bit] Bit where
  toFun M := M 0 0 + M 1 1 + M 2 1
  map_add' := by intro M N; simp; ring
  map_smul' := by intro a M; simp; ring

noncomputable def pointTrace : pointMatrixSpace →ₗ[Bit] Bit :=
  pointTraceRaw.comp pointMatrixSpace.subtype

theorem pointTrace_identity : pointTrace pointIdentity = 0 := by
  change pointTraceRaw (1 : BinaryMatrix) = 0
  decide +kernel

theorem pointScalarLine_le_trace_kernel : pointScalarLine ≤ pointTrace.ker := by
  apply Submodule.span_le.mpr
  rintro x (rfl : x = pointIdentity)
  exact pointTrace_identity

noncomputable def translationTrace : PointTranslationSpace →ₗ[Bit] Bit :=
  pointScalarLine.liftQ pointTrace pointScalarLine_le_trace_kernel

theorem mem_pointMatrixSpace_iff (M : BinaryMatrix) :
    M ∈ pointMatrixSpace ↔
      matrixAt M (rowLabel 0).val = (M 1 1 + M 1 2) • (rowLabel 0).val := by
  change pointMatrixConstraints M = 0 ↔ _
  constructor
  · intro h
    have h0 := congrArg (fun v : Fin 2 → Bit => v 0) h
    have h1 := congrArg (fun v : Fin 2 → Bit => v 1) h
    simp [pointMatrixConstraints] at h0 h1
    ext i
    fin_cases i <;> simp [matrixAt, rowLabel, binaryLabel, Fin.sum_univ_succ]
    · exact h0
    · linear_combination (norm := ring_nf) h1
      rw [show (2 : Bit) = 0 by decide]
      simp
  · intro h
    have h0 := congrArg (fun v : E => v 0) h
    have h2 := congrArg (fun v : E => v 2) h
    simp [matrixAt, rowLabel, binaryLabel, Fin.sum_univ_succ] at h0 h2
    ext i
    fin_cases i <;> simp [pointMatrixConstraints]
    · exact h0
    · linear_combination (norm := ring_nf) h2
      rw [show (2 : Bit) = 0 by decide]
      simp

/-- The existing projective matrix quotient contains this point-fixing subquotient. -/
noncomputable def pointTranslationInclusion : PointTranslationSpace →ₗ[Bit] ProjectiveTranslationModule :=
  pointScalarLine.liftQ (matrixScalarLine.mkQ.comp pointMatrixSpace.subtype) (by
    apply Submodule.span_le.mpr
    rintro x (rfl : x = pointIdentity)
    change matrixScalarLine.mkQ (1 : BinaryMatrix) = 0
    exact (Submodule.Quotient.mk_eq_zero matrixScalarLine).mpr
      (Submodule.subset_span (Set.mem_singleton _)))

theorem pointTranslationInclusion_injective : Function.Injective pointTranslationInclusion := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro x hx
  obtain ⟨M, rfl⟩ := pointScalarLine.mkQ_surjective x
  have hM : matrixScalarLine.mkQ M.val = 0 := hx
  obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton (R := Bit)).mp
    ((Submodule.Quotient.mk_eq_zero matrixScalarLine).mp hM)
  change pointScalarLine.mkQ M = 0
  apply (Submodule.Quotient.mk_eq_zero pointScalarLine).mpr
  exact (Submodule.mem_span_singleton (R := Bit)).mpr ⟨a, Subtype.ext ha⟩

/-- Quotient coordinates on E/<p>: the reference p=(0,1,1) maps to zero. -/
def planeProjection : E →ₗ[Bit] (Fin 2 → Bit) where
  toFun v := ![v 0, v 1 + v 2]
  map_add' := by intro v w; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a v; ext i; fin_cases i <;> simp <;> ring

def inducedPlaneMatrix (M : BinaryMatrix) : Matrix (Fin 2) (Fin 2) Bit :=
  !![M 0 0, M 0 1; M 1 0 + M 2 0, M 1 1 + M 2 1]

theorem inducedPlaneMatrix_trace (M : BinaryMatrix) :
    Matrix.trace (inducedPlaneMatrix M) = pointTraceRaw M := by
  simp [Matrix.trace, Matrix.diag, inducedPlaneMatrix, pointTraceRaw, Fin.sum_univ_succ]
  ring

theorem inducedPlaneMatrix_action (M : pointMatrixSpace) (v : E) :
    planeProjection (matrixAt M.val v) =
      (inducedPlaneMatrix M.val).mulVec (planeProjection v) := by
  have h0 := congrArg (fun w : Fin 2 → Bit => w 0) M.prop
  have h1 := congrArg (fun w : Fin 2 → Bit => w 1) M.prop
  simp [pointMatrixSpace, pointMatrixConstraints] at h0 h1
  ext i
  fin_cases i <;>
    simp [planeProjection, matrixAt, inducedPlaneMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  · linear_combination (norm := ring_nf) v 2 * h0
    simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_mul, neg_zero, add_zero, zero_add, sub_self]
  · linear_combination (norm := ring_nf) v 2 * h1
    simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_mul, neg_zero, add_zero, zero_add, sub_self]

end Atlas.Tits
