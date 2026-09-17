import Atlas.Algebra.IcosianReductionNorm
import Atlas.Algebra.IcosianNormOneGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra

def icosianNormOneToOrder : icosianNormOneGroup →* icosianOrder where
  toFun u := ⟨u.val.val,u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual scalar
 norm-one group reduces to determinant-one matrices. -/
def icosianNormOneReduction : icosianNormOneGroup →*
    Matrix.SpecialLinearGroup (Fin 2) GoldenFour where
  toFun u := ⟨icosianModuloTwo ⟨u.val.val,u.property⟩,by
    rw [icosianModuloTwo_det]
    have h : icosianIntegralNorm ⟨u.val.val,u.property⟩=1 :=
      (icosianIntegralNorm_eq_one _).mpr (icosianNormOneGroup_norm u)
    rw [h,map_one]⟩
  map_one' := by
    apply Subtype.ext
    change icosianModuloTwo (1 : icosianOrder)=1
    exact map_one icosianModuloTwo
  map_mul' u v := by
    apply Subtype.ext
    change icosianModuloTwo (⟨u.val.val,u.property⟩*⟨v.val.val,v.property⟩)=_
    exact map_mul icosianModuloTwo _ _

theorem icosianNormOneReduction_apply (u : icosianNormOneGroup) :
    (icosianNormOneReduction u).val=icosianModuloTwo ⟨u.val.val,u.property⟩ := rfl

end Atlas.Algebra
