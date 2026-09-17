import Atlas.LinearGroups.Orthogonal.D2MatrixAction
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # The actual trace-zero conjugation construction of rank-one B -/
noncomputable section
namespace Atlas.Orthogonal.B1Conjugation
open Matrix
variable {F : Type*} [Field F]
abbrev Mat := Matrix (Fin 2) (Fin 2) F
abbrev SL := SpecialLinearGroup (Fin 2) F
abbrev TraceZero := LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F)

set_option maxHeartbeats 1200000 in
def coordinates : VectorB 1 F ≃ₗ[F] TraceZero (F := F) where
  toFun v := ⟨!![v.2,v.1 (.inl 0);v.1 (.inr 0),-v.2],by simp [Matrix.trace, Fin.sum_univ_two]⟩
  invFun M := (Sum.elim ![M.val 0 1] ![M.val 1 0],M.val 0 0)
  left_inv v := by
    apply Prod.ext
    · ext i; rcases i with i|i <;> fin_cases i <;> rfl
    · rfl
  right_inv M := by
    apply Subtype.ext
    have h : M.val 0 0 + M.val 1 1 = 0 := by
      have hh := M.prop
      change M.val.trace = 0 at hh
      simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using hh
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · exact (eq_neg_of_add_eq_zero_right h).symm
  map_add' u v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · exact neg_add u.2 v.2
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · exact (smul_neg c v.2).symm

theorem coordinates_form (v : VectorB 1 F) : -(coordinates v).val.det = formB 1 F v := by
  simp [coordinates, Matrix.det_fin_two, formB_apply, formD_apply, Fin.sum_univ_one]
  ring

theorem conjugation_trace (g : SL (F := F)) (M : Mat (F := F)) :
    (g.val * M * g⁻¹.val).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, one_mul]

def kernelMap (g : SL (F := F)) : TraceZero (F := F) →ₗ[F] TraceZero (F := F) where
  toFun M := ⟨g.val * M.val * g⁻¹.val,by
    change (g.val * M.val * g⁻¹.val).trace = 0
    rw [conjugation_trace]
    exact M.prop⟩
  map_add' M N := Subtype.ext (by simp [mul_add,add_mul])
  map_smul' c M := Subtype.ext (by simp [Matrix.mul_smul,Matrix.smul_mul])

theorem kernelMap_mul (g h : SL (F := F)) :
    kernelMap (g*h) = (kernelMap g).comp (kernelMap h) := by
  apply LinearMap.ext
  intro M
  apply Subtype.ext
  change (g*h).val * M.val * (g*h)⁻¹.val = g.val * (h.val * M.val * h⁻¹.val) * g⁻¹.val
  rw [_root_.mul_inv_rev,SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_mul]
  simp only [mul_assoc]

@[simp] theorem kernelMap_one : kernelMap (1 : SL (F := F)) = LinearMap.id := by
  apply LinearMap.ext
  intro M
  apply Subtype.ext
  change (1 : SL (F := F)).val * M.val * (1 : SL (F := F))⁻¹.val = M.val
  rw [inv_one,SpecialLinearGroup.coe_one,one_mul,mul_one]

def kernelAction (g : SL (F := F)) : TraceZero (F := F) ≃ₗ[F] TraceZero (F := F) where
  __ := kernelMap g
  invFun := kernelMap g⁻¹
  left_inv M := by
    change ((kernelMap g⁻¹).comp (kernelMap g)) M = M
    rw [← kernelMap_mul,inv_mul_cancel,kernelMap_one,LinearMap.id_apply]
  right_inv M := by
    change ((kernelMap g).comp (kernelMap g⁻¹)) M = M
    rw [← kernelMap_mul,mul_inv_cancel,kernelMap_one,LinearMap.id_apply]

def onB (g : SL (F := F)) : VectorB 1 F ≃ₗ[F] VectorB 1 F :=
  coordinates.trans ((kernelAction g).trans coordinates.symm)

theorem onB_coordinates (g : SL (F := F)) (v : VectorB 1 F) :
    (coordinates (onB g v)).val = g.val * (coordinates v).val * g⁻¹.val :=
  congrArg Subtype.val (coordinates.apply_symm_apply (kernelAction g (coordinates v)))

theorem onB_form (g : SL (F := F)) (v : VectorB 1 F) : formB 1 F (onB g v) = formB 1 F v := by
  rw [← coordinates_form,← coordinates_form,onB_coordinates,Matrix.det_mul,Matrix.det_mul,
    g.det_coe,g⁻¹.det_coe,one_mul,mul_one]

def toOrthogonal : SL (F := F) →* O_B 1 F where
  toFun g := ⟨onB g,onB_form g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates.symm (kernelMap 1 (coordinates v)) = v
    rw [kernelMap_one,LinearMap.id_apply,LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates.symm (kernelMap (g*h) (coordinates v)) =
      coordinates.symm (kernelMap g (coordinates (coordinates.symm (kernelMap h (coordinates v)))))
    rw [LinearEquiv.apply_symm_apply,kernelMap_mul,LinearMap.comp_apply]

end Atlas.Orthogonal.B1Conjugation
