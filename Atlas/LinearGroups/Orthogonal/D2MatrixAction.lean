import Atlas.LinearGroups.Orthogonal.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Actual determinant model for split D2 -/
noncomputable section
namespace Atlas.Orthogonal.D2Matrix
open Matrix
variable {F : Type*} [Field F]
abbrev Mat := Matrix (Fin 2) (Fin 2) F
abbrev PairSL := Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F

/-- The determinant coordinates retain the two ordered hyperbolic pairs. -/
def coordinates : VectorD 2 F ≃ₗ[F] Mat (F := F) where
  toFun v := !![v (.inl 0),v (.inl 1);-v (.inr 1),v (.inr 0)]
  invFun M := Sum.elim ![M 0 0,M 0 1] ![M 1 1,-M 1 0]
  left_inv v := by ext i; rcases i with i|i <;> fin_cases i <;> simp
  right_inv M := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' u v := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coordinates_det (v : VectorD 2 F) : (coordinates v).det = formD 2 F v := by
  simp [coordinates,Matrix.det_fin_two,formD_apply,Fin.sum_univ_succ]

/-- The determinant quadratic form on the actual matrix space. -/
def determinantForm : QuadraticForm F (Mat (F := F)) :=
  (formD 2 F).comp coordinates.symm.toLinearMap

theorem determinantForm_apply (M : Mat (F := F)) : determinantForm M = M.det := by
  change formD 2 F (coordinates.symm M) = M.det
  exact (coordinates_det (coordinates.symm M)).symm.trans
    (congrArg Matrix.det (coordinates.apply_symm_apply M))

/-- The actual split quadratic space is isometric to two-by-two determinant space. -/
def coordinatesIsometry : (formD 2 F).IsometryEquiv (determinantForm (F := F)) where
  __ := coordinates
  map_app' v := by
    change formD 2 F (coordinates.symm (coordinates v)) = formD 2 F v
    rw [LinearEquiv.symm_apply_apply]

def matrixAction (g : PairSL (F := F)) : Mat (F := F) ≃ₗ[F] Mat (F := F) where
  toFun M := g.1.val * M * g.2⁻¹.val
  invFun M := g.1⁻¹.val * M * g.2.val
  left_inv M := by
    change g.1⁻¹.val * (g.1.val * M * g.2⁻¹.val) * g.2.val = M
    calc
      _ = (g.1⁻¹.val*g.1.val)*M*(g.2⁻¹.val*g.2.val) := by simp only [mul_assoc]
      _ = M := by rw [← SpecialLinearGroup.coe_mul,← SpecialLinearGroup.coe_mul,
        inv_mul_cancel,inv_mul_cancel,SpecialLinearGroup.coe_one,one_mul,mul_one]
  right_inv M := by
    change g.1.val * (g.1⁻¹.val * M * g.2.val) * g.2⁻¹.val = M
    calc
      _ = (g.1.val*g.1⁻¹.val)*M*(g.2.val*g.2⁻¹.val) := by simp only [mul_assoc]
      _ = M := by rw [← SpecialLinearGroup.coe_mul,← SpecialLinearGroup.coe_mul,
        mul_inv_cancel,mul_inv_cancel,SpecialLinearGroup.coe_one,one_mul,mul_one]
  map_add' M N := by simp [mul_add,add_mul]
  map_smul' c M := by simp [Matrix.mul_smul,Matrix.smul_mul]

theorem matrixAction_det (g : PairSL (F := F)) (M : Mat (F := F)) :
    (matrixAction g M).det = M.det := by
  change (g.1.val*M*g.2⁻¹.val).det = _
  rw [Matrix.det_mul,Matrix.det_mul,g.1.det_coe,g.2⁻¹.det_coe,one_mul,mul_one]

def onD (g : PairSL (F := F)) : VectorD 2 F ≃ₗ[F] VectorD 2 F :=
  coordinates.trans ((matrixAction g).trans coordinates.symm)

theorem onD_form (g : PairSL (F := F)) (v : VectorD 2 F) :
    formD 2 F (onD g v) = formD 2 F v := by
  rw [← coordinates_det,← coordinates_det]
  change (coordinates (coordinates.symm (matrixAction g (coordinates v)))).det = _
  rw [LinearEquiv.apply_symm_apply,matrixAction_det]

def toOrthogonal : PairSL (F := F) →* O_DPlus 2 F where
  toFun g := ⟨onD g,onD_form g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates.symm ((1 : SpecialLinearGroup (Fin 2) F).val * coordinates v *
      (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val) = v
    rw [inv_one,SpecialLinearGroup.coe_one,one_mul,mul_one,LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates.symm ((g.1*h.1).val*coordinates v*(g.2*h.2)⁻¹.val) =
      coordinates.symm (g.1.val*coordinates (coordinates.symm
        (h.1.val*coordinates v*h.2⁻¹.val))*g.2⁻¹.val)
    rw [LinearEquiv.apply_symm_apply,_root_.mul_inv_rev,SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul]
    simp only [mul_assoc]

theorem toOrthogonal_coordinates (g : PairSL (F := F)) (v : VectorD 2 F) :
    coordinates ((toOrthogonal g).val v) = g.1.val*coordinates v*g.2⁻¹.val :=
  coordinates.apply_symm_apply _
end Atlas.Orthogonal.D2Matrix
