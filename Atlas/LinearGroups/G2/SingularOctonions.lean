import Atlas.Algebra.SplitOctonion.Basic
import Atlas.LinearGroups.G2.SingularCoordinateCount

/-! The coordinate fibre count transported to the actual split octonion algebra. -/
noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion
variable (F : Type*) [Field F]

abbrev SingularOctonions := {x : Carrier F // trace x = 0 ∧ norm x = 0}
abbrev NonzeroSingularOctonions := {x : SingularOctonions F // x.val ≠ 0}

/-- Solve trace zero by setting the fifth coordinate equal to minus the fourth. -/
def singularOctonionsEquivCoordinates : SingularOctonions F ≃ SingularCoordinates F where
  toFun x := ⟨(![x.val 0,x.val 1,x.val 2], ![x.val 7,x.val 6,x.val 5], x.val 3), by
    have ht : x.val 4 = -x.val 3 := eq_neg_of_add_eq_zero_right x.prop.1
    have hn := x.prop.2
    simp only [SplitOctonion.norm, ht] at hn
    simp only [DotProduct.functional_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    linear_combination hn⟩
  invFun p := ⟨![p.val.1 0,p.val.1 1,p.val.1 2,p.val.2.2,-p.val.2.2,
      p.val.2.1 2,p.val.2.1 1,p.val.2.1 0], by
    constructor
    · simp [trace]
    · have hp := p.prop
      simp only [DotProduct.functional_apply, Fin.sum_univ_succ,
        Fin.sum_univ_zero, add_zero] at hp
      change p.val.1 0 * p.val.2.1 0 +
        (p.val.1 1 * p.val.2.1 1 + p.val.1 2 * p.val.2.1 2) = p.val.2.2 ^ 2 at hp
      simp only [SplitOctonion.norm]
      simp
      linear_combination hp⟩
  left_inv x := by
    apply Subtype.ext
    have ht : x.val 4 = -x.val 3 := eq_neg_of_add_eq_zero_right x.prop.1
    funext i
    fin_cases i <;> simp [ht]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl

theorem singularOctonionsEquivCoordinates_zero_iff (x : SingularOctonions F) :
    (singularOctonionsEquivCoordinates F x).val = 0 ↔ x.val = 0 := by
  constructor
  · intro h
    have he := congrArg (fun p => (singularOctonionsEquivCoordinates F).symm p)
      (show singularOctonionsEquivCoordinates F x = ⟨0, by simp⟩ from Subtype.ext h)
    rw [Equiv.symm_apply_apply] at he
    have hv := congrArg Subtype.val he
    funext i
    have hvi := congrFun hv i
    fin_cases i <;> simpa [singularOctonionsEquivCoordinates] using hvi
  · intro h
    simp [singularOctonionsEquivCoordinates, h]

def nonzeroSingularOctonionsEquivCoordinates :
    NonzeroSingularOctonions F ≃ NonzeroSingularCoordinates F :=
  (singularOctonionsEquivCoordinates F).subtypeEquiv fun x =>
    not_congr (singularOctonionsEquivCoordinates_zero_iff F x).symm

theorem card_singularOctonions [Finite F] :
    Nat.card (SingularOctonions F) = Nat.card F ^ 6 := by
  rw [Nat.card_congr (singularOctonionsEquivCoordinates F), card_singularCoordinates]

theorem card_nonzeroSingularOctonions [Finite F] :
    Nat.card (NonzeroSingularOctonions F) = Nat.card F ^ 6 - 1 := by
  rw [Nat.card_congr (nonzeroSingularOctonionsEquivCoordinates F),
    card_nonzeroSingularCoordinates]

end Atlas.G2
