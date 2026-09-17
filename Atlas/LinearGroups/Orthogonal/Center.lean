import Atlas.LinearGroups.Orthogonal.ElementaryCentralizer
import Atlas.LinearAlgebra.QuadraticWittTwo

/-! # Intrinsic scalar description of the elementary orthogonal center -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
open scoped IsMulCommutative
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q) (hQ : Q.polarBilin.Nondegenerate)

include H hQ in
theorem elementary_centralizer_scalar_of_frame (z : isometrySubgroup Q)
    (hz : ∀ g ∈ elementarySubgroup Q, g*z = z*g) :
    ∃ c : F, ∀ x : V, z.val x = c • x := by
  let a : complement Q H.e₁ H.f₁ := ⟨H.e₂, H.ee, H.ef⟩
  let b : complement Q H.e₁ H.f₁ := ⟨H.f₂, H.fe, H.ff⟩
  exact elementary_centralizer_scalar Q hQ H.e₁ H.f₁ H.qe₁ H.qf₁ H.pair₁ a b H.qe₂ H.pair₂ z hz

include H hQ in
/-- The center is exactly the scalar isometries which actually belong to E. -/
theorem mem_elementary_center_iff_scalar (z : elementarySubgroup Q) :
    z ∈ Subgroup.center (elementarySubgroup Q) ↔
      ∃ c : F, c^2 = 1 ∧ ∀ x : V, z.val.val x = c • x := by
  constructor
  · intro hz
    have hcomm (g : isometrySubgroup Q) (hg : g ∈ elementarySubgroup Q) : g*z.val = z.val*g := by
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨g, hg⟩)
    obtain ⟨c, hc⟩ := elementary_centralizer_scalar_of_frame Q H hQ z.val hcomm
    have hv : Q (H.e₁ + H.f₁) = 1 := by
      rw [QuadraticMap.map_add Q H.e₁ H.f₁]
      change Q H.e₁ + Q H.f₁ + Q.polarBilin H.e₁ H.f₁ = 1
      rw [H.qe₁, H.qf₁, H.pair₁, zero_add, zero_add]
    have h := z.val.prop (H.e₁+H.f₁)
    rw [hc, Q.map_smul, hv, smul_eq_mul, mul_one, ← pow_two] at h
    exact ⟨c, h, hc⟩
  · rintro ⟨c, _, hc⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.val.val (z.val.val x) = z.val.val (g.val.val x)
    rw [hc, hc, map_smul]

include H hQ in
/-- Noncommutativity of E follows already from its root geometry, in every characteristic. -/
theorem elementary_noncommutative_of_frame : ¬ IsMulCommutative (elementarySubgroup Q) := by
  intro hcomm
  letI := hcomm
  have hea : Q.polarBilin H.e₁ H.e₂ = 0 := (polar_swap Q _ _).trans H.ee
  let r := siegelElement Q H.e₁ H.e₂ H.qe₁ hea
  let z : elementarySubgroup Q := ⟨r, siegelElement_mem _ _ _ _ _⟩
  have hz : z ∈ Subgroup.center (elementarySubgroup Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact mul_comm g z
  obtain ⟨c, _, hc⟩ := (mem_elementary_center_iff_scalar Q H hQ z).mp hz
  have he : z.val.val H.e₁ = H.e₁ := siegel_fix Q H.e₁ H.e₂ H.qe₁ hea
  have hc1 : c = 1 := by
    have h := congrArg (fun y => Q.polarBilin y H.f₁) ((hc H.e₁).symm.trans he)
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, H.pair₁, mul_one] using h
  have hr : siegel Q H.e₁ H.e₂ H.f₁ = H.f₁ := by
    change z.val.val H.f₁ = H.f₁
    rw [hc, hc1, one_smul]
  have hfa : Q.polarBilin H.f₁ H.e₂ = 0 := (polar_swap Q _ _).trans H.ef
  have hfe : Q.polarBilin H.f₁ H.e₁ = 1 := (polar_swap Q _ _).trans H.pair₁
  simp only [siegel, hfa, hfe, H.qe₂, zero_smul, add_zero, one_smul, zero_mul, sub_zero] at hr
  have ha : H.e₂ = 0 := sub_eq_self.mp hr
  have hp := H.pair₂
  rw [ha, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp
end Atlas.Orthogonal
