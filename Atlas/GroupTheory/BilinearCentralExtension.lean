import Mathlib.GroupTheory.Solvable
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! Two-step groups defined by a biadditive central cocycle.
This generic construction contains no sporadic or Lie-type group assumptions. -/
namespace Atlas.GroupTheory
variable {V Z : Type*} [AddCommGroup V] [AddCommGroup Z]

@[ext] structure BilinearExtension (b : V →+ V →+ Z) where
  point : V
  central : Z

namespace BilinearExtension
variable (b : V →+ V →+ Z)

instance : Group (BilinearExtension b) where
  mul x y := ⟨x.point+y.point,x.central+y.central+b x.point y.point⟩
  one := ⟨0,0⟩
  inv x := ⟨-x.point,-x.central+b x.point x.point⟩
  mul_assoc x y z := by
    apply BilinearExtension.ext
    · exact add_assoc _ _ _
    · change (x.central+y.central+b x.point y.point)+z.central+
        b (x.point+y.point) z.point =
        x.central+(y.central+z.central+b y.point z.point)+b x.point (y.point+z.point)
      simp only [map_add,AddMonoidHom.add_apply]
      abel
  one_mul x := by
    apply BilinearExtension.ext
    · exact zero_add _
    · change 0+x.central+b 0 x.point=x.central
      simp
  mul_one x := by
    apply BilinearExtension.ext
    · exact add_zero _
    · change x.central+0+b x.point 0=x.central
      simp
  inv_mul_cancel x := by
    apply BilinearExtension.ext
    · exact neg_add_cancel _
    · change (-x.central+b x.point x.point)+x.central+b (-x.point) x.point=0
      simp only [map_neg,AddMonoidHom.neg_apply]
      abel

def project : BilinearExtension b →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.point
  map_one' := rfl
  map_mul' _ _ := rfl

def centralEmbedding : Multiplicative Z →* BilinearExtension b where
  toFun z := ⟨0,z.toAdd⟩
  map_one' := rfl
  map_mul' z w := by
    apply BilinearExtension.ext
    · change (0 : V)=0+0
      simp
    · change z.toAdd+w.toAdd=z.toAdd+w.toAdd+b 0 0
      simp

theorem ker_project_le_range : (project b).ker ≤ (centralEmbedding b).range := by
  intro x hx
  have h : x.point=0 := congrArg Multiplicative.toAdd hx
  refine ⟨Multiplicative.ofAdd x.central,?_⟩
  apply BilinearExtension.ext
  · exact h.symm
  · rfl

theorem centralEmbedding_injective : Function.Injective (centralEmbedding b) := by
  intro z w h
  exact congrArg (fun x => Multiplicative.ofAdd x.central) h

theorem project_surjective : Function.Surjective (project b) := by
  intro v
  exact ⟨⟨v.toAdd,0⟩,rfl⟩

theorem ker_project_eq_range : (project b).ker=(centralEmbedding b).range := by
  apply le_antisymm (ker_project_le_range b)
  rintro x ⟨z,rfl⟩
  rfl

theorem centralEmbedding_commute (z : Multiplicative Z) (x : BilinearExtension b) :
    Commute (centralEmbedding b z) x := by
  change centralEmbedding b z*x=x*centralEmbedding b z
  apply BilinearExtension.ext
  · change 0+x.point=x.point+0
    simp
  · change z.toAdd+x.central+b 0 x.point=x.central+z.toAdd+b x.point 0
    simp [add_comm]

instance : Group.IsSolvable
 (BilinearExtension b) :=
  Group.isSolvable_of_ker_le_range (centralEmbedding b) (project b) (ker_project_le_range b)

def parameterEquiv : BilinearExtension b ≃ V×Z where
  toFun x := (x.point,x.central)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card : Nat.card (BilinearExtension b)=Nat.card V*Nat.card Z := by
  rw [Nat.card_congr (parameterEquiv b),Nat.card_prod]

end BilinearExtension
end Atlas.GroupTheory
