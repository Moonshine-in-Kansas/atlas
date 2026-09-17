import Atlas.Codes.IcosianGlue
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
namespace Atlas.Codes
open Matrix

/-- Actual information coordinates for the three-dimensional Morita image. -/
def icosianGlueLinearEquiv (F : Type*) [Field F] :
    (Fin 3 → F) ≃ₗ[F] icosianGlue F where
  toFun p := ⟨icosianGlueEncoder (p 0) (p 1) (p 2),icosianGlueEncoder_mem _ _ _⟩
  invFun x := ![x.val 0 0,x.val 1 0,x.val 2 1]
  left_inv p := by funext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    funext i j
    rcases x.property with ⟨h0,h1,h2⟩
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h0.trans h1).symm
    · rfl
    · exact h1.symm
    · change -x.val 0 0-x.val 1 0=x.val 2 0
      linear_combination -h2
    · rfl
  map_add' p q := by
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [icosianGlueEncoder,Matrix.cons_val_two] <;> ring
  map_smul' r p := by
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [icosianGlueEncoder,Matrix.cons_val_two,smul_eq_mul,mul_sub,mul_neg]

theorem icosianGlue_finrank {F : Type*} [Field F] :
    Module.finrank F (icosianGlue F)=3 := by
  rw [← (icosianGlueLinearEquiv F).finrank_eq]
  simp

theorem icosianGlue_card {F : Type*} [Field F] [Finite F] :
    Nat.card (icosianGlue F)=Nat.card F^3 := by
  rw [← Nat.card_congr (icosianGlueLinearEquiv F).toEquiv,Nat.card_fun]
  simp

theorem icosianGlue_card_four {F : Type*} [Field F] [Finite F] (hF : Nat.card F=4) :
    Nat.card (icosianGlue F)=64 := by
  rw [icosianGlue_card,hF]
  norm_num

end Atlas.Codes
