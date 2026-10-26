import Atlas.Comparisons.Exceptional.E6.DiscriminantFixer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The actual faithful binary matrix reduction of the integral Weyl group. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Matrix

abbrev IntegralWeyl := ↥(weyl ℤ)

def integralMatrix : IntegralWeyl →* GeneralLinearGroup (Fin 6) ℤ :=
  ((GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (Fin 6 → ℤ))).symm.toMonoidHom).comp
    ((Atlas.Orthogonal.isometrySubgroup (form ℤ)).subtype.comp (weyl ℤ).subtype)

theorem integralMatrix_val (g : IntegralWeyl) :
    (integralMatrix g).val = LinearMap.toMatrix' g.val.val.toLinearMap := rfl

def binaryMatrix : IntegralWeyl →* GeneralLinearGroup (Fin 6) (ZMod 2) :=
  (GeneralLinearGroup.map (Int.castRingHom (ZMod 2))).comp integralMatrix

theorem binaryMatrix_action (g : IntegralWeyl) (x : Fin 6 → ℤ) :
    (binaryMatrix g).val *ᵥ reduceBinary x = reduceBinary (g.val.val x) := by
  change (integralMatrix g).val.map (Int.castRingHom (ZMod 2)) *ᵥ
    (fun i => (x i : ZMod 2)) = _
  rw [integralMatrix_val]
  funext i
  exact ((Int.castRingHom (ZMod 2)).map_mulVec
    (LinearMap.toMatrix' g.val.val.toLinearMap) x i).symm.trans (by
      rw [LinearMap.toMatrix'_mulVec]
      rfl)

theorem binaryMatrix_injective : Function.Injective binaryMatrix := by
  apply (MonoidHom.ker_eq_bot_iff binaryMatrix).mp
  apply bot_unique
  intro g hg
  change g = 1
  apply weyl_binary_kernel
  intro x
  have he := binaryMatrix_action g x
  have hval : (binaryMatrix g).val = 1 := congrArg Units.val hg
  rw [hval,Matrix.one_mulVec] at he
  exact he.symm

end Atlas.Comparisons.E6Lattice
