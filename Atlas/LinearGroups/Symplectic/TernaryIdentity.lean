import Atlas.LinearGroups.Symplectic.AbelianImages

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [CharP F 3]

/-- Four orthogonal-direction transvections cancel in characteristic three. -/
theorem ternary_four_transvections (u v : Vector n F) (huv : form u v = 0) :
    transvection u 1 * transvection v 1 * transvection (u+v) 1 * transvection (u-v) 1 = 1 := by
  have hvu : form v u = 0 := by rw [form_swap,huv,neg_zero]
  apply ext_action
  intro x
  simp only [mul_smul,one_smul,transvection_apply]
  simp only [map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,smul_eq_mul,form_self,huv,hvu,add_zero,zero_add,
    sub_self,sub_zero,mul_zero,zero_mul,one_mul]
  funext i
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring_nf
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  rw [hc,mul_zero,mul_zero,add_zero,add_zero]

end Atlas.Symplectic
