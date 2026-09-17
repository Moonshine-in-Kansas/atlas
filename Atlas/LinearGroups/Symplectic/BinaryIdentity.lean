import Atlas.LinearGroups.Symplectic.AbelianImages

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2]

/-- The seven nonzero directions of an isotropic three-space give a symbolic relation. -/
theorem binary_seven_transvections (u v w : Vector n F)
    (huv : form u v = 0) (huw : form u w = 0) (hvw : form v w = 0) :
    transvection u 1 * transvection v 1 * transvection w 1 * transvection (u+v) 1 *
      transvection (u+w) 1 * transvection (v+w) 1 * transvection (u+v+w) 1 = 1 := by
  have hvu : form v u = 0 := by rw [form_swap,huv,neg_zero]
  have hwu : form w u = 0 := by rw [form_swap,huw,neg_zero]
  have hwv : form w v = 0 := by rw [form_swap,hvw,neg_zero]
  apply ext_action
  intro x
  simp only [mul_smul,one_smul,transvection_apply]
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    form_self,huv,huw,hvw,hvu,hwu,hwv,add_zero,zero_add,mul_zero,zero_mul,one_mul]
  funext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring_nf
  have hc2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hc4 : (4 : F) = 0 := by linear_combination 2*hc2
  simp only [hc2,hc4,mul_zero,add_zero]

end Atlas.Symplectic
