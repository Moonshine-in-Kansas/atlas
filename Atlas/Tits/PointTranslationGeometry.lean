import Atlas.Tits.PointTranslationSpace
import Atlas.Rudvalis.PointFixingTranslations

namespace Atlas.Tits
open Atlas.Rudvalis

theorem pointMatrixSpace_iff_fixes_pair (M : BinaryMatrix) :
    M ∈ pointMatrixSpace ↔ FixesCoordinatePair (rowLabel 0) M := by
  rw [mem_pointMatrixSpace_iff]
  constructor
  · intro h
    rcases Atlas.Codes.bit_cases (M 1 1 + M 1 2) with h0 | h1
    · exact Or.inl (by simpa [h0] using h)
    · exact Or.inr (by simpa [h1] using h)
  · rintro (h | h)
    · have ha := congrArg (fun v : E => v 1) h
      simp [matrixAt, rowLabel, binaryLabel, Fin.sum_univ_succ] at ha
      simpa [ha] using h
    · have ha := congrArg (fun v : E => v 1) h
      simp [matrixAt, rowLabel, binaryLabel, Fin.sum_univ_succ] at ha
      simpa [ha] using h

theorem pointMatrixSpace_iff_fixes_cross (M : BinaryMatrix) (x : E) :
    M ∈ pointMatrixSpace ↔
      coordinateCross (coordinateTranslation M (rowLabel 0, x)) =
        coordinateCross (rowLabel 0, x) := by
  rw [pointMatrixSpace_iff_fixes_pair, translation_fixes_coordinateCross_iff]

noncomputable def pointTraceWitness : pointMatrixSpace :=
  ⟨!![1,0,0; 0,0,0; 0,0,0], by
    change pointMatrixConstraints _ = 0
    decide +kernel⟩

theorem pointTrace_witness : pointTrace pointTraceWitness = 1 := by
  change pointTraceRaw _ = 1
  decide +kernel

theorem translationTrace_surjective : Function.Surjective translationTrace := by
  intro b
  refine ⟨pointScalarLine.mkQ (b • pointTraceWitness), ?_⟩
  change pointTrace (b • pointTraceWitness) = b
  rw [map_smul, pointTrace_witness, smul_eq_mul, mul_one]

theorem translationTrace_kernel_finrank : Module.finrank Bit translationTrace.ker = 5 := by
  have h := translationTrace.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr translationTrace_surjective] at h
  have hr : Module.finrank Bit (⊤ : Submodule Bit Bit) = 1 := by simp
  rw [hr, pointTranslationSpace_finrank] at h
  omega

end Atlas.Tits
