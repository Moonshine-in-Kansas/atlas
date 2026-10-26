import Atlas.LinearGroups.F4.Basic
import Atlas.Algebra.Albert.StabilizerInvariants
import Atlas.LinearAlgebra.ProjectiveConeCount
import Mathlib.LinearAlgebra.Projectivization.Action

noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable (F : Type*) [Field F]

abbrev WhiteZeroPoints :=
  {p : ℙ F (Carrier F) // trace p.rep = 0 ∧ adjoint p.rep = 0}

theorem whiteZero_smul_iff (a : Fˣ) (x : Carrier F) :
    (trace (a • x) = 0 ∧ adjoint (a • x) = 0) ↔
      (trace x = 0 ∧ adjoint x = 0) := by
  have ht : trace (a • x) = a.val * trace x := by
    simp [trace, Units.smul_def, _root_.mul_add]
  rw [ht]
  simp [Units.smul_def, adjoint_smul, a.ne_zero]

def whiteZeroPointMk (x : Carrier F) (hx : x ≠ 0)
    (ht : trace x = 0) (ha : adjoint x = 0) : WhiteZeroPoints F :=
  Atlas.LinearAlgebra.conePointMk (fun x : Carrier F => trace x = 0 ∧ adjoint x = 0)
    (whiteZero_smul_iff F) ⟨x,hx,ht,ha⟩

def basePoint : WhiteZeroPoints F :=
  whiteZeroPointMk F baseVector baseVector_ne_zero baseVector_trace baseVector_adjoint

instance whiteZeroPointsAction : MulAction (Model F) (WhiteZeroPoints F) where
  smul g p := ⟨g.val • p.val, by
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    apply (Atlas.LinearAlgebra.cone_mk_iff
      (fun x : Carrier F => trace x = 0 ∧ adjoint x = 0)
      (whiteZero_smul_iff F) _ _).mpr
    simpa only [LinearEquiv.smul_def, stabilizer_trace, stabilizer_adjoint,
      p.property.2, map_zero] using p.property⟩
  one_smul p := Subtype.ext (one_smul _ _)
  mul_smul g h p := Subtype.ext (mul_smul g.val h.val p.val)

def pointStabilizer : Subgroup (Model F) := MulAction.stabilizer (Model F) (basePoint F)

def nonzeroConeEquivWhiteZeroVectors :
    Atlas.LinearAlgebra.NonzeroCone (fun x : Carrier F => trace x = 0 ∧ adjoint x = 0) ≃
      WhiteZeroVectors F where
  toFun x := ⟨x.val, ⟨x.property.1, x.property.2.2⟩, x.property.2.1⟩
  invFun x := ⟨x.val, x.property.1.1, x.property.2, x.property.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def nonzeroWhiteEquivPointsUnits : WhiteZeroVectors F ≃ WhiteZeroPoints F × Fˣ :=
  (nonzeroConeEquivWhiteZeroVectors F).symm.trans
    (Atlas.LinearAlgebra.nonzeroConeEquivPointsUnits _ (whiteZero_smul_iff F))

end Atlas.F4
