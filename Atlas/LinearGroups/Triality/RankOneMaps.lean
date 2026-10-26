import Atlas.LinearGroups.Triality.SplitBlocks
import Atlas.LinearGroups.Triality.Basic

/-! Concrete rank-one homomorphisms into the split eight-dimensional isometry group. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Matrix
variable {K : Type*} [Field K]

def signMatrix (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![g 0 0,-g 0 1;-g 1 0,g 1 1]

/-- Conjugation by diag(1,-1), written without a characteristic restriction. -/
def signTwist : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨signMatrix g.val, by
    have h := g.det_coe
    rw [det_fin_two] at h
    simpa [signMatrix, det_fin_two] using h⟩
  map_one' := by
    apply Subtype.ext
    change signMatrix (1 : Matrix (Fin 2) (Fin 2) K) = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [signMatrix]
  map_mul' g h := by
    apply Subtype.ext
    change signMatrix (g.val*h.val) = signMatrix g.val * signMatrix h.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The contragredient SL₂ homomorphism. -/
def contragredient : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  map_one' := by
    apply Subtype.ext
    simp only [inv_one, SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_one, Matrix.transpose_one]
  map_mul' g h := by
    apply Subtype.ext
    simp only [ _root_.mul_inv_rev, SpecialLinearGroup.coe_transpose,
      SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Three outer SL₂ factors, with the prescribed Frobenius twists. -/
def rankOneShortOrthogonal : SpecialLinearGroup (Fin 2) K →* O_DPlus 4 K :=
  blockEmbedding.comp
    (((D2Matrix.toOrthogonal).comp ((1 : SpecialLinearGroup (Fin 2) K →*
      SpecialLinearGroup (Fin 2) K).prod contragredient)).prod
    ((D2Matrix.toOrthogonal).comp
      ((signTwist.comp (SpecialLinearGroup.map
        ((FiniteCubic.sigma F K).toRingHom.comp (FiniteCubic.sigma F K).toRingHom))).prod
      (contragredient.comp (SpecialLinearGroup.map (FiniteCubic.sigma F K).toRingHom)))))


end Atlas.Triality
