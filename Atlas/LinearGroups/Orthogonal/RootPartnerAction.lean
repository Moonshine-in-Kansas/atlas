import Atlas.LinearGroups.Orthogonal.RootSubgroupCoordinates
import Atlas.LinearAlgebra.QuadraticPairCount

/-! # Regular action of a singular-line root subgroup on normalized partners -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V) (he : Q e = 0) (hf : Q f = 0)
  (hef : Q.polarBilin e f = 1)

theorem rootComplement_partner (w : complement Q e f) :
    (rootComplementHom Q e f he (Multiplicative.ofAdd w)).val f =
      ((partnerEquivComplement Q e f he hf hef).symm (-w)).val := by
  change siegel Q e w.val f = -Q (-w.val) • e + (1 : F) • f + -w.val
  have hfw : Q.polarBilin f w.val = 0 := (polar_swap Q f w.val).trans w.prop.2
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  simp only [siegel, hfw, hfe, zero_smul, add_zero, one_smul, mul_one, QuadraticMap.map_neg]
  module

/-- The actual root-group element is uniquely determined by its value at the partner. -/
def rootPartnerEquiv : rootSubgroup Q e he ≃
    {x : V // Q x = 0 ∧ Q.polarBilin e x = 1} :=
  (rootComplementEquiv Q e f he hef).symm.toEquiv.trans
    (Multiplicative.toAdd.trans ((Equiv.neg _).trans
      (partnerEquivComplement Q e f he hf hef).symm))

theorem rootPartnerEquiv_apply (g : rootSubgroup Q e he) :
    (rootPartnerEquiv Q e f he hf hef g).val = g.val.val f := by
  obtain ⟨w, rfl⟩ := (rootComplementEquiv Q e f he hef).surjective g
  change ((partnerEquivComplement Q e f he hf hef).symm
    (-((rootComplementEquiv Q e f he hef).symm
      ((rootComplementEquiv Q e f he hef) w)).toAdd)).val = _
  rw [MulEquiv.symm_apply_apply]
  exact (rootComplement_partner Q e f he hf hef w.toAdd).symm

include hf hef in
/-- Sharp transitivity, proved by actual additive coordinates, in every characteristic. -/
theorem root_unique_partner_transport (x : V) (hx : Q x = 0)
    (hex : Q.polarBilin e x = 1) :
    ∃! g : rootSubgroup Q e he, g.val.val f = x := by
  obtain ⟨g, hg⟩ := (rootPartnerEquiv Q e f he hf hef).surjective ⟨x, hx, hex⟩
  have hval : g.val.val f = x := by
    rw [← rootPartnerEquiv_apply Q e f he hf hef g]
    exact congrArg Subtype.val hg
  refine ⟨g, hval, ?_⟩
  intro k hk
  apply (rootPartnerEquiv Q e f he hf hef).injective
  apply Subtype.ext
  rw [rootPartnerEquiv_apply, rootPartnerEquiv_apply, hk, hval]
end Atlas.Orthogonal
