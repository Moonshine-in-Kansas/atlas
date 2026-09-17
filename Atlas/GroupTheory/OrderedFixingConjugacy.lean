import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Tactic.Group

namespace Atlas.GroupTheory

def orderedFixingConjugacy {G X I : Type*} [Group G] [MulAction G X]
    (e f : I → X) (g : G) (hg : ∀ i, g • e i = f i) :
    fixingSubgroup G (Set.range e) ≃* fixingSubgroup G (Set.range f) where
  toFun t := ⟨g*t.val*g⁻¹,by
    intro x
    obtain ⟨i,hi⟩ := x.prop
    change (g*t.val*g⁻¹) • x.val = x.val
    rw [← hi,← hg i,mul_smul,mul_smul,inv_smul_smul]
    rw [show t.val • e i = e i from t.prop ⟨e i,⟨i,rfl⟩⟩]⟩
  invFun t := ⟨g⁻¹*t.val*g,by
    intro x
    obtain ⟨i,hi⟩ := x.prop
    change (g⁻¹*t.val*g) • x.val = x.val
    rw [← hi,mul_smul,mul_smul,hg]
    rw [show t.val • f i = f i from t.prop ⟨f i,⟨i,rfl⟩⟩,← hg,inv_smul_smul]⟩
  left_inv t := by apply Subtype.ext; dsimp; group
  right_inv t := by apply Subtype.ext; dsimp; group
  map_mul' s t := by apply Subtype.ext; dsimp; group

end Atlas.GroupTheory
