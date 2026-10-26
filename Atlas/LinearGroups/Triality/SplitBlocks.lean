import Atlas.LinearGroups.Orthogonal.D2MatrixAction
import Mathlib.Tactic

/-! Two determinant blocks in the prescribed split eight-coordinate space. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {K : Type*} [Field K]

def splitBlocks : VectorD 4 K ≃ₗ[K] VectorD 2 K × VectorD 2 K where
  toFun x := (Sum.elim ![x (.inl 0),x (.inl 1)] ![x (.inr 0),x (.inr 1)],
    Sum.elim ![x (.inl 2),x (.inl 3)] ![x (.inr 2),x (.inr 3)])
  invFun p := Sum.elim
    ![p.1 (.inl 0),p.1 (.inl 1),p.2 (.inl 0),p.2 (.inl 1)]
    ![p.1 (.inr 0),p.1 (.inr 1),p.2 (.inr 0),p.2 (.inr 1)]
  left_inv x := by ext i; rcases i with i|i <;> fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext <;> ext i <;> rcases i with i|i <;> fin_cases i <;> rfl
  map_add' x y := by
    apply Prod.ext <;> ext i <;> rcases i with i|i <;> fin_cases i <;> rfl
  map_smul' c x := by
    apply Prod.ext <;> ext i <;> rcases i with i|i <;> fin_cases i <;> rfl

theorem splitBlocks_form (x : VectorD 4 K) :
    formD 4 K x = formD 2 K (splitBlocks x).1 + formD 2 K (splitBlocks x).2 := by
  simp [formD_apply, Fin.sum_univ_succ, splitBlocks]
  ring

def blockLinear (g : O_DPlus 2 K × O_DPlus 2 K) : VectorD 4 K ≃ₗ[K] VectorD 4 K :=
  splitBlocks.trans ((g.1.val.prodCongr g.2.val).trans splitBlocks.symm)

theorem blockLinear_form (g : O_DPlus 2 K × O_DPlus 2 K) (x : VectorD 4 K) :
    formD 4 K (blockLinear g x) = formD 4 K x := by
  rw [splitBlocks_form, splitBlocks_form x]
  change formD 2 K (splitBlocks (splitBlocks.symm _)).1 +
    formD 2 K (splitBlocks (splitBlocks.symm _)).2 = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg₂ (·+·) (g.1.property _) (g.2.property _)

def blockEmbedding : (O_DPlus 2 K × O_DPlus 2 K) →* O_DPlus 4 K where
  toFun g := ⟨blockLinear g,blockLinear_form g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change splitBlocks.symm (splitBlocks x) = x
    exact splitBlocks.symm_apply_apply x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change blockLinear (g*h) x = blockLinear g (blockLinear h x)
    apply splitBlocks.injective
    simp only [blockLinear, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.prodCongr_apply]
    rfl

end Atlas.Triality
