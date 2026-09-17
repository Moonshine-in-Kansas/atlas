import Atlas.LinearGroups.Orthogonal.RootSubgroupConjugation
import Mathlib.Tactic.Module

/-! # Two coordinate roots connect orthogonal hyperbolic pairs -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem two_root_cross_transport (Q : QuadraticForm F V)
    (H : Subgroup (isometrySubgroup Q)) (e f u v : V)
    (he : Q e = 0) (hf : Q f = 0) (hu : Q u = 0) (hv : Q v = 0)
    (hef : Q.polarBilin e f = 1) (huv : Q.polarBilin u v = 1)
    (heu : Q.polarBilin e u = 0) (hev : Q.polarBilin e v = 0)
    (hfu : Q.polarBilin f u = 0)
    (hrf : rootSubgroup Q f hf ≤ H) (hrv : rootSubgroup Q v hv ≤ H) :
    ∃ g : isometrySubgroup Q, g ∈ H ∧ g.val e = -u := by
  have hve : Q.polarBilin v e = 0 := (polar_swap Q v e).trans hev
  have hvne : Q.polarBilin v (-e) = 0 := by rw [map_neg,hve,neg_zero]
  let a := siegelElement Q f u hf hfu
  let b := siegelElement Q v (-e) hv hvne
  have ha : a ∈ H := hrf ⟨Multiplicative.ofAdd ⟨u,hfu⟩,rfl⟩
  have hb : b ∈ H := hrv ⟨Multiplicative.ofAdd ⟨-e,hvne⟩,rfl⟩
  have hae : a.val e = e-u := by
    change siegel Q f u e = e-u
    simp [siegel,heu,hef,hu]
  have hee : Q.polarBilin e e = 0 := by rw [polar_self,he,mul_zero]
  have hue : Q.polarBilin u e = 0 := (polar_swap Q u e).trans heu
  refine ⟨b*a,H.mul_mem hb ha,?_⟩
  change b.val (a.val e) = -u
  rw [hae]
  change siegel Q v (-e) (e-u) = -u
  simp only [siegel,map_sub,map_neg,LinearMap.sub_apply,hee,hue,hev,huv,
    Q.map_neg,he,sub_zero,sub_self,neg_zero,zero_smul,zero_mul,zero_sub,
    neg_smul,one_smul]
  module

end Atlas.Orthogonal
