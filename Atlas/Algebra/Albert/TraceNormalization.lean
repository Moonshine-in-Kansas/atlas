import Atlas.Algebra.Albert.RankOne

/-! Normalizing a nonzero trace by its actual scalar value. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F]

theorem trace_smul (a : F) (x : Carrier F) : trace (a • x)=a*trace x := by
  simp [trace,_root_.mul_add]

def nonzeroTraceEquiv : {x : Carrier F // adjoint x=0 ∧ trace x≠0} ≃
    Fˣ × TraceOneRankOne F where
  toFun x := (Units.mk0 (trace x.val) x.prop.2,
    ⟨(trace x.val)⁻¹ • x.val,by rw [adjoint_smul,x.prop.1,smul_zero],by
      rw [trace_smul,inv_mul_cancel₀ x.prop.2]⟩)
  invFun p := ⟨p.1.val • p.2.val,by rw [adjoint_smul,p.2.prop.1,smul_zero],by
    rw [trace_smul,p.2.prop.2,mul_one]; exact p.1.ne_zero⟩
  left_inv x := by
    apply Subtype.ext
    change (trace x.val) • ((trace x.val)⁻¹ • x.val)=x.val
    rw [smul_smul,mul_inv_cancel₀ x.prop.2,one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Units.ext
      change trace (p.1.val • p.2.val)=p.1.val
      rw [trace_smul,p.2.prop.2,mul_one]
    · apply Subtype.ext
      change (trace (p.1.val • p.2.val))⁻¹ • (p.1.val • p.2.val)=p.2.val
      rw [trace_smul,p.2.prop.2,mul_one,smul_smul,inv_mul_cancel₀ p.1.ne_zero,one_smul]

end Atlas.Albert
