import Atlas.Algebra.Albert.RankOne
import Atlas.Algebra.SplitOctonion.NormComposition
import Mathlib.Tactic.LinearCombination

/-! The first diagonal open chart of the actual adjoint-zero cone. -/
namespace Atlas.Albert
variable {F : Type*} [Field F]

def rankOneChart (a : F) (B C : SplitOctonion.Carrier F) : Carrier F :=
  (![a,a⁻¹*SplitOctonion.norm C,a⁻¹*SplitOctonion.norm B],
    ![a⁻¹ • SplitOctonion.conjugate (SplitOctonion.mul B C),B,C])

theorem rankOneChart_adjoint (a : F) (ha : a≠0) (B C : SplitOctonion.Carrier F) :
    adjoint (rankOneChart a B C)=0 := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [rankOneChart,adjoint,SplitOctonion.norm_smul,SplitOctonion.norm_conjugate,
        SplitOctonion.norm_mul] <;> field_simp [ha] <;> ring
  · funext i
    fin_cases i <;>
      simp [rankOneChart,adjoint,SplitOctonion.mul_smul,SplitOctonion.smul_mul,
        SplitOctonion.conjugate_smul,SplitOctonion.conjugate_mul_conjugate_product_left,
        SplitOctonion.conjugate_mul_conjugate_product_right,smul_smul,ha]

theorem eq_rankOneChart_of_adjoint_zero (x : Carrier F) (hx : adjoint x=0) (ha : x.1 0≠0) :
    x=rankOneChart (x.1 0) (x.2 1) (x.2 2) := by
  have hb : x.1 0*x.1 1=SplitOctonion.norm (x.2 2) := by
    have h := congrArg (fun y : Carrier F=>y.1 2) hx
    exact sub_eq_zero.mp h
  have hc : x.1 2*x.1 0=SplitOctonion.norm (x.2 1) := by
    have h := congrArg (fun y : Carrier F=>y.1 1) hx
    exact sub_eq_zero.mp h
  have hA : SplitOctonion.conjugate (SplitOctonion.mul (x.2 1) (x.2 2))=x.1 0 • x.2 0 := by
    have h := congrArg (fun y : Carrier F=>y.2 0) hx
    exact sub_eq_zero.mp h
  apply Prod.ext
  · funext i; fin_cases i
    · rfl
    · change x.1 1=(x.1 0)⁻¹*SplitOctonion.norm (x.2 2)
      rw [←hb,←mul_assoc,inv_mul_cancel₀ ha,one_mul]
    · change x.1 2=(x.1 0)⁻¹*SplitOctonion.norm (x.2 1)
      rw [←hc,mul_comm (x.1 2),←mul_assoc,inv_mul_cancel₀ ha,one_mul]
  · funext i; fin_cases i
    · change x.2 0=(x.1 0)⁻¹ • SplitOctonion.conjugate (SplitOctonion.mul (x.2 1) (x.2 2))
      rw [hA,smul_smul,inv_mul_cancel₀ ha,one_smul]
    · rfl
    · rfl

noncomputable def rankOneChartEquiv :
    (Fˣ × SplitOctonion.Carrier F × SplitOctonion.Carrier F) ≃
      {x : Carrier F // adjoint x=0 ∧ x.1 0≠0} where
  toFun p := ⟨rankOneChart p.1.val p.2.1 p.2.2,
    rankOneChart_adjoint p.1.val p.1.ne_zero p.2.1 p.2.2,p.1.ne_zero⟩
  invFun x := (Units.mk0 (x.val.1 0) x.prop.2,x.val.2 1,x.val.2 2)
  left_inv p := by apply Prod.ext; apply Units.ext; rfl; rfl
  right_inv x := Subtype.ext (eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2).symm

theorem rankOneChart_trace_zero_iff (a : F) (ha : a≠0) (B C : SplitOctonion.Carrier F) :
    trace (rankOneChart a B C)=0 ↔ SplitOctonion.norm B+SplitOctonion.norm C= -a^2 := by
  change a+a⁻¹*SplitOctonion.norm C+a⁻¹*SplitOctonion.norm B=0 ↔ _
  rw [←mul_eq_zero_iff_left ha]
  have he : a*(a+a⁻¹*SplitOctonion.norm C+a⁻¹*SplitOctonion.norm B)=
      a^2+SplitOctonion.norm B+SplitOctonion.norm C := by field_simp [ha]; ring
  rw [he]
  constructor <;> intro h <;> linear_combination h

end Atlas.Albert
