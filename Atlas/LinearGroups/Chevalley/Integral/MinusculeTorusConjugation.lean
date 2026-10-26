import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylTorus
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
/-! Same-root torus conjugation in literal Strings. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} (S : Strings I Ω) (R : Type*) [CommRing R]

theorem torusEquiv_mul_raising (i : I) (a : Rˣ) (s : R) :
    S.torusEquiv R i a * S.rootEquiv R i (-1) (by decide) s =
      S.rootEquiv R i (-1) (by decide) (a.val^2*s) * S.torusEquiv R i a := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply, LinearEquiv.coe_coe]
  rcases S.minuscule i μ with h | h | h
  all_goals
    simp [rootEquiv, transvection_apply, step_single, h, map_add, map_smul,
      S.torusEquiv_single, S.pairing_reflection, Finsupp.smul_single,
      smul_eq_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem torusEquiv_mul_lowering (i : I) (a : Rˣ) (s : R) :
    S.torusEquiv R i a * S.rootEquiv R i 1 (by decide) s =
      S.rootEquiv R i 1 (by decide) (a.inv^2*s) * S.torusEquiv R i a := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply, LinearEquiv.coe_coe]
  rcases S.minuscule i μ with h | h | h
  all_goals
    simp [rootEquiv, transvection_apply, step_single, h, map_add, map_smul,
      S.torusEquiv_single, S.pairing_reflection, Finsupp.smul_single,
      smul_eq_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]

variable [Fintype Ω] [DecidableEq Ω]

def equivMatrixHom : (OrbitModule (Ω := Ω) R ≃ₗ[R] OrbitModule (Ω := Ω) R) →*
    (Matrix Ω Ω R)ˣ :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (OrbitModule (Ω := Ω) R)).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne).toMulEquiv)).toMonoidHom

theorem equivMatrixHom_root (i : I) (ε : ℤ) (hε : ε ≠ 0) (s : R) :
    equivMatrixHom R (S.rootEquiv R i ε hε s) = S.rootMatrixUnit R i ε hε s := by
  apply Units.ext
  change LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (S.transvection R i ε s) = S.rootMatrix R i ε s
  exact (S.rootMatrix_eq_toMatrix R i ε s).symm

def weylMatrixUnit (i : I) (a : Rˣ) : (Matrix Ω Ω R)ˣ :=
  S.rootMatrixUnit R i (-1) (by decide) a.val *
    S.rootMatrixUnit R i 1 (by decide) (-a.inv) *
      S.rootMatrixUnit R i (-1) (by decide) a.val

def torusMatrixUnit (i : I) (a : Rˣ) : (Matrix Ω Ω R)ˣ :=
  S.weylMatrixUnit R i a * (S.weylMatrixUnit R i 1)⁻¹

theorem equivMatrixHom_weyl (i : I) (a : Rˣ) :
    equivMatrixHom R (S.weylEquiv R i a) = S.weylMatrixUnit R i a := by
  simp only [weylEquiv, weylMatrixUnit, map_mul, equivMatrixHom_root]

theorem equivMatrixHom_torus (i : I) (a : Rˣ) :
    equivMatrixHom R (S.torusEquiv R i a) = S.torusMatrixUnit R i a := by
  simp only [torusEquiv, torusMatrixUnit, map_mul, map_inv, equivMatrixHom_weyl]

theorem torusMatrixUnit_mul_raising (i : I) (a : Rˣ) (s : R) :
    S.torusMatrixUnit R i a * S.rootMatrixUnit R i (-1) (by decide) s =
      S.rootMatrixUnit R i (-1) (by decide) (a.val^2*s) * S.torusMatrixUnit R i a := by
  have h := congrArg (equivMatrixHom R) (S.torusEquiv_mul_raising R i a s)
  simpa only [map_mul, equivMatrixHom_root, equivMatrixHom_torus] using h

theorem torusMatrixUnit_mul_lowering (i : I) (a : Rˣ) (s : R) :
    S.torusMatrixUnit R i a * S.rootMatrixUnit R i 1 (by decide) s =
      S.rootMatrixUnit R i 1 (by decide) (a.inv^2*s) * S.torusMatrixUnit R i a := by
  have h := congrArg (equivMatrixHom R) (S.torusEquiv_mul_lowering R i a s)
  simpa only [map_mul, equivMatrixHom_root, equivMatrixHom_torus] using h
end Atlas.Chevalley.Integral.Minuscule.Strings
