import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section
namespace Atlas.GroupTheory
open MulAction
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem stabilizer_orbit_smul (g : G) (a : X) (x y : Y)
    (h : y ∈ orbit (stabilizer G a) x) :
    g • y ∈ orbit (stabilizer G (g • a)) (g • x) := by
  obtain ⟨r,hr⟩ := mem_orbit_iff.mp h
  let s := stabilizerEquivStabilizer (rfl : g • a = g • a) r
  refine mem_orbit_iff.mpr ⟨s,?_⟩
  change (s.val : G) • (g • x) = g • y
  rw [stabilizerEquivStabilizer_apply]
  simp only [MulAut.conj_apply,mul_smul,inv_smul_smul]
  exact congrArg (fun z : Y => g • z) hr

def stabilizerOrbitTransport (g : G) (a : X) (x : Y) :
    orbit (stabilizer G a) x ≃ orbit (stabilizer G (g • a)) (g • x) where
  toFun y := ⟨g • y.val,stabilizer_orbit_smul g a x y.val y.prop⟩
  invFun y := ⟨g⁻¹ • y.val,by
    convert
      stabilizer_orbit_smul g⁻¹ (g • a) (g • x) y.val y.prop using 1
    rw [inv_smul_smul,inv_smul_smul]⟩
  left_inv y := Subtype.ext (inv_smul_smul g y.val)
  right_inv y := Subtype.ext (smul_inv_smul g y.val)

end Atlas.GroupTheory
