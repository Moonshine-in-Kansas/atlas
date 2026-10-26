import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Restrict a genuine conjugation action along an injective linear map.
Existence of actual linear-automorphism lifts is explicit. Uniqueness makes
their choice a homomorphism; no faithfulness of the ambient representation is needed. -/
noncomputable section
namespace Atlas.LinearAlgebra
variable {R V A G : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Ring A] [Module R A] [Group G]
variable (ρ : G →* A) (γ : V →ₗ[R] A) (H : Subgroup (V ≃ₗ[R] V))

def ConjugationCompatible (g : G) (h : H) : Prop :=
  ∀ v, ρ g * γ v * ρ g⁻¹ = γ (h.val v)

theorem conjugationCompatible_one : ConjugationCompatible ρ γ H 1 1 := by
  intro v
  change ρ 1 * γ v * ρ ((1 : G)⁻¹) = γ v
  simp only [map_one, inv_one, one_mul, mul_one]

theorem conjugationCompatible_mul {g k : G} {h l : H}
    (hg : ConjugationCompatible ρ γ H g h)
    (hk : ConjugationCompatible ρ γ H k l) :
    ConjugationCompatible ρ γ H (g*k) (h*l) := by
  intro v
  change ρ (g*k) * γ v * ρ ((g*k)⁻¹) = γ (h.val (l.val v))
  rw [mul_inv_rev, map_mul, map_mul]
  calc
    (ρ g * ρ k) * γ v * (ρ k⁻¹ * ρ g⁻¹) =
        ρ g * (ρ k * γ v * ρ k⁻¹) * ρ g⁻¹ := by simp only [mul_assoc]
    _ = γ (h.val (l.val v)) := by rw [hk v, hg (l.val v)]

theorem conjugationCompatible_unique (hγ : Function.Injective γ)
    {g : G} {h l : H} (hh : ConjugationCompatible ρ γ H g h)
    (hl : ConjugationCompatible ρ γ H g l) : h=l := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact hγ ((hh v).symm.trans (hl v))

/-- The actual induced action on the injected module, once existence of lifts
has been proved. No kernel or injectivity assertion about ρ is included. -/
def conjugationRestrictionHom (hγ : Function.Injective γ)
    (hex : ∀ g, ∃ h : H, ConjugationCompatible ρ γ H g h) : G →* H where
  toFun g := Classical.choose (hex g)
  map_one' := conjugationCompatible_unique ρ γ H hγ
    (Classical.choose_spec (hex 1)) (conjugationCompatible_one ρ γ H)
  map_mul' g k := conjugationCompatible_unique ρ γ H hγ
    (Classical.choose_spec (hex (g*k)))
    (conjugationCompatible_mul ρ γ H
      (Classical.choose_spec (hex g)) (Classical.choose_spec (hex k)))

theorem conjugationRestrictionHom_compatible (hγ : Function.Injective γ)
    (hex : ∀ g, ∃ h : H, ConjugationCompatible ρ γ H g h) (g : G) :
    ConjugationCompatible ρ γ H g (conjugationRestrictionHom ρ γ H hγ hex g) :=
  Classical.choose_spec (hex g)

theorem conjugationRestrictionHom_eq (hγ : Function.Injective γ)
    (hex : ∀ g, ∃ h : H, ConjugationCompatible ρ γ H g h)
    (g : G) (h : H) (hh : ConjugationCompatible ρ γ H g h) :
    conjugationRestrictionHom ρ γ H hγ hex g = h :=
  conjugationCompatible_unique ρ γ H hγ
    (conjugationRestrictionHom_compatible ρ γ H hγ hex g) hh

end Atlas.LinearAlgebra
