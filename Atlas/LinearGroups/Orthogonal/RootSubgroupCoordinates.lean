import Atlas.LinearGroups.Orthogonal.RootSubgroup
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finiteness

/-! # Faithful additive coordinates for a singular-line Siegel subgroup -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u f : V) (hu : Q u = 0)
  (huf : Q.polarBilin u f = 1)

def rootComplementHom : Multiplicative (complement Q u f) →* isometrySubgroup Q where
  toFun v := siegelElement Q u v.toAdd.val hu
    ((polar_swap Q u v.toAdd.val).trans v.toAdd.prop.1)
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact siegel_zero Q u x
  map_mul' v w := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (siegel_add Q u v.toAdd.val w.toAdd.val x hu
      ((polar_swap Q u v.toAdd.val).trans v.toAdd.prop.1)
      ((polar_swap Q u w.toAdd.val).trans w.toAdd.prop.1)).symm

include huf in
theorem rootComplementHom_injective : Function.Injective (rootComplementHom Q u f hu) := by
  apply (injective_iff_map_eq_one _).mpr
  intro v hv
  let w : rootParameterSpace Q u :=
    ⟨v.toAdd.val, (polar_swap Q u v.toAdd.val).trans v.toAdd.prop.1⟩
  obtain ⟨c, hc⟩ := (rootParameter_kernel Q u hu f huf w).mp hv
  have hf := v.toAdd.prop.2
  change Q.polarBilin v.toAdd.val f = 0 at hf
  change v.toAdd.val = c • u at hc
  rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, huf, mul_one] at hf
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change v.toAdd.val = 0
  rw [hc, hf, zero_smul]

/-- Subtracting the partner coordinate chooses the unique perpendicular representative. -/
def rootPerpendicularRepresentative (v : rootParameterSpace Q u) : complement Q u f :=
  ⟨v.val - Q.polarBilin v.val f • u, by
    have huu : Q.polarBilin u u = 0 := by rw [polar_self, hu, mul_zero]
    have hvu : Q.polarBilin v.val u = 0 := (polar_swap Q v.val u).trans v.prop
    constructor
    · change Q.polarBilin (v.val-Q.polarBilin v.val f • u) u = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, huu, smul_zero, hvu, sub_zero]
    · change Q.polarBilin (v.val-Q.polarBilin v.val f • u) f = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, huf, smul_eq_mul, mul_one, sub_self]⟩

theorem rootPerpendicularRepresentative_element (v : rootParameterSpace Q u) :
    rootComplementHom Q u f hu (Multiplicative.ofAdd (rootPerpendicularRepresentative Q u f hu huf v)) =
      rootParameterHom Q u hu (Multiplicative.ofAdd v) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel Q u (v.val-Q.polarBilin v.val f • u) x = siegel Q u v.val x
  rw [sub_eq_add_neg, ← neg_smul]
  exact siegel_parameter_mod_line Q u v.val x _ hu v.prop

include huf in
theorem rootComplementHom_range : (rootComplementHom Q u f hu).range = rootSubgroup Q u hu := by
  ext g
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.ofAdd ⟨v.toAdd.val, (polar_swap Q u v.toAdd.val).trans v.toAdd.prop.1⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.ofAdd (rootPerpendicularRepresentative Q u f hu huf v.toAdd),
      rootPerpendicularRepresentative_element Q u f hu huf v.toAdd⟩

/-- Faithful additive coordinates on the actual singular-line subgroup. -/
def rootComplementEquiv : Multiplicative (complement Q u f) ≃* rootSubgroup Q u hu :=
  (MonoidHom.ofInjective (rootComplementHom_injective Q u f hu huf)).trans
    (MulEquiv.subgroupCongr (rootComplementHom_range Q u f hu huf))

include huf in
theorem card_rootSubgroup [Finite F] [FiniteDimensional F V] (hf : Q f = 0) :
    Nat.card (rootSubgroup Q u hu) = Nat.card F ^ (Module.finrank F V - 2) := by
  have hd := finrank_complement Q u f hu hf huf
  have hd' : Module.finrank F (complement Q u f) = Module.finrank F V - 2 := by omega
  rw [← Nat.card_congr (rootComplementEquiv Q u f hu huf).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := F), hd']

end Atlas.Orthogonal

