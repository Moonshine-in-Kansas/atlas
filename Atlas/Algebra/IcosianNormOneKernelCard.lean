import Atlas.Algebra.IcosianNormOneKernel
import Mathlib.Data.Fintype.Card

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra Matrix

def icosianNormOneMinusOne : icosianNormOneGroup :=
  icosianNormOneGroupOf (-1) (icosianOrder.neg_mem icosianOrder.one_mem) (by
    change Quaternion.normSq (-1 : IcosianQuaternion)=1
    rw [Quaternion.normSq_neg,map_one])

theorem icosianNormOne_value_injective :
    Function.Injective (fun u : icosianNormOneGroup => u.val.val) := by
  intro u v h
  apply Subtype.ext
  exact Subtype.ext h

theorem icosianNormOneMinusOne_ne_one : icosianNormOneMinusOne≠1 := by
  intro h
  have he := congrArg (fun u : icosianNormOneGroup => u.val.val.re.re) h
  change (-1 : ℚ)=1 at he
  norm_num at he

theorem icosianNormOneReduction_minus_one :
    icosianNormOneReduction icosianNormOneMinusOne=1 := by
  apply Subtype.ext
  change icosianModuloTwo (-1 : icosianOrder)=1
  rw [map_neg,map_one]
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;> simp [Matrix.one_apply] <;> decide

attribute [local instance] Classical.propDecidable

def icosianNormOneKernelEquiv : icosianNormOneReduction.ker ≃ Bool where
  toFun u := if u.val=1 then false else true
  invFun b := if b then ⟨icosianNormOneMinusOne,icosianNormOneReduction_minus_one⟩ else 1
  left_inv u := by
    apply Subtype.ext
    by_cases h : u.val=1
    · simp [h]
    · have hv := icosianNormOneReduction_kernel_values u.val u.property
      have he : u.val=icosianNormOneMinusOne := by
        apply icosianNormOne_value_injective
        rcases hv with hv | hv
        · exact False.elim (h (icosianNormOne_value_injective hv))
        · exact hv
      simp [h,he,icosianNormOneMinusOne_ne_one]
  right_inv b := by
    cases b <;> simp [icosianNormOneMinusOne_ne_one]

theorem icosianNormOneReduction_kernel_card : Nat.card icosianNormOneReduction.ker=2 := by
  rw [Nat.card_congr icosianNormOneKernelEquiv]
  simp

end Atlas.Algebra
