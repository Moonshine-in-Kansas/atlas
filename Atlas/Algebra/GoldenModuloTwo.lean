import Atlas.Algebra.IcosianIntegralCoordinates
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Algebra
open scoped QuadraticAlgebra

abbrev GoldenFour := QuadraticAlgebra (ZMod 2) 1 1

instance goldenFour_irreducible : Fact (∀ r : ZMod 2, r^2≠1+1*r) := ⟨by decide⟩

def goldenFourTau : GoldenFour := QuadraticAlgebra.omega

def goldenModuloTwo : GoldenInteger →+* GoldenFour where
  toFun z := ⟨z.re,z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp

theorem goldenModuloTwo_surjective : Function.Surjective goldenModuloTwo := by
  intro x
  refine ⟨⟨x.re.val,x.im.val⟩,?_⟩
  ext <;> simp [goldenModuloTwo]

theorem goldenModuloTwo_eq_zero (x : GoldenInteger) :
    goldenModuloTwo x=0 ↔ 2∣x.re ∧ 2∣x.im := by
  rw [QuadraticAlgebra.ext_iff]
  simp [goldenModuloTwo, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem goldenFourTau_sq : goldenFourTau^2=1+goldenFourTau := by
  ext <;> norm_num [goldenFourTau,QuadraticAlgebra.omega,pow_two]

end Atlas.Algebra
