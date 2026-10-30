import Atlas.LinearAlgebra.ConjugationRestriction
import Atlas.GroupTheory.SubgroupSurjectionCard

/-! The subgroup of ambient elements with an actual prescribed conjugation
lift. An injective linear intertwiner makes the lift unique. Independent finite
orders then extend its surjective homomorphism to the full ambient group.
No centralizer, simplicity, presentation, or ambient faithfulness premise occurs. -/
noncomputable section
namespace Atlas.LinearAlgebra
variable {R V A G : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Ring A] [Module R A] [Group G]
variable (ρ : G →* A) (γ : V →ₗ[R] A) (H : Subgroup (V ≃ₗ[R] V))

theorem conjugationCompatible_inv {g : G} {h : H}
    (hg : ConjugationCompatible ρ γ H g h) :
    ConjugationCompatible ρ γ H g⁻¹ h⁻¹ := by
  intro v
  have hv : ρ g * γ (h.val.symm v) * ρ g⁻¹ = γ v := by
    simpa only [LinearEquiv.apply_symm_apply] using hg (h.val.symm v)
  change ρ g⁻¹ * γ v * ρ (g⁻¹)⁻¹ = γ (h.val.symm v)
  rw [inv_inv, ← hv]
  calc
    ρ g⁻¹ * (ρ g * γ (h.val.symm v) * ρ g⁻¹) * ρ g =
        (ρ g⁻¹ * ρ g) * γ (h.val.symm v) * (ρ g⁻¹ * ρ g) := by
          simp only [mul_assoc]
    _ = γ (h.val.symm v) := by
      have hi : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      simp only [hi, one_mul, mul_one]

/-- Actual ambient elements admitting a lift in the specified linear group. -/
def conjugationLiftSubgroup : Subgroup G where
  carrier := {g | ∃ h : H, ConjugationCompatible ρ γ H g h}
  one_mem' := ⟨1, conjugationCompatible_one ρ γ H⟩
  mul_mem' := by
    rintro g k ⟨h, hh⟩ ⟨l, hl⟩
    exact ⟨h*l, conjugationCompatible_mul ρ γ H hh hl⟩
  inv_mem' := by
    rintro g ⟨h, hh⟩
    exact ⟨h⁻¹, conjugationCompatible_inv ρ γ H hh⟩

/-- This is the existing conjugation restriction construction applied only to
the subgroup on which lift existence has actually been established. -/
def conjugationLiftHom (hγ : Function.Injective γ) :
    conjugationLiftSubgroup ρ γ H →* H :=
  conjugationRestrictionHom
    (ρ.comp (conjugationLiftSubgroup ρ γ H).subtype) γ H hγ
    (fun g => g.property)

theorem conjugationLiftHom_compatible (hγ : Function.Injective γ)
    (g : conjugationLiftSubgroup ρ γ H) :
    ConjugationCompatible ρ γ H g.val (conjugationLiftHom ρ γ H hγ g) :=
  conjugationRestrictionHom_compatible
    (ρ.comp (conjugationLiftSubgroup ρ γ H).subtype) γ H hγ
    (fun g => g.property) g

theorem conjugationLiftHom_eq (hγ : Function.Injective γ)
    (g : conjugationLiftSubgroup ρ γ H) (h : H)
    (hh : ConjugationCompatible ρ γ H g.val h) :
    conjugationLiftHom ρ γ H hγ g = h :=
  conjugationCompatible_unique ρ γ H hγ
    (conjugationLiftHom_compatible ρ γ H hγ g) hh

theorem conjugationLiftHom_surjective (hγ : Function.Injective γ)
    (hex : ∀ h : H, ∃ g : G, ConjugationCompatible ρ γ H g h) :
    Function.Surjective (conjugationLiftHom ρ γ H hγ) := by
  intro h
  obtain ⟨g, hg⟩ := hex h
  exact ⟨⟨g, h, hg⟩, conjugationLiftHom_eq ρ γ H hγ ⟨g, h, hg⟩ h hg⟩

/-- It suffices to lift an actual generating set of the target. -/
theorem conjugationLiftHom_surjective_of_generators (hγ : Function.Injective γ)
    (S : Set H) (hS : Subgroup.closure S = ⊤)
    (hex : ∀ h ∈ S, ∃ g : G, ConjugationCompatible ρ γ H g h) :
    Function.Surjective (conjugationLiftHom ρ γ H hγ) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hS]
  apply (Subgroup.closure_le _).mpr
  intro h hh
  obtain ⟨g, hg⟩ := hex h hh
  exact ⟨⟨g, h, hg⟩, conjugationLiftHom_eq ρ γ H hγ ⟨g, h, hg⟩ h hg⟩

section Finite
variable [Finite G]

def conjugationLiftEquiv (hγ : Function.Injective γ)
    (hs : Function.Surjective (conjugationLiftHom ρ γ H hγ))
    (hc : Nat.card G = Nat.card H) : G ≃* H :=
  Atlas.GroupTheory.subgroupSurjectionEquiv (conjugationLiftSubgroup ρ γ H)
    (conjugationLiftHom ρ γ H hγ) hs hc

theorem conjugationLiftEquiv_eq (hγ : Function.Injective γ)
    (hs : Function.Surjective (conjugationLiftHom ρ γ H hγ))
    (hc : Nat.card G = Nat.card H) (g : G) (h : H)
    (hh : ConjugationCompatible ρ γ H g h) :
    conjugationLiftEquiv ρ γ H hγ hs hc g = h := by
  let x : conjugationLiftSubgroup ρ γ H := ⟨g, h, hh⟩
  exact (Atlas.GroupTheory.subgroupSurjectionEquiv_apply
    (conjugationLiftSubgroup ρ γ H) (conjugationLiftHom ρ γ H hγ) hs hc x).trans
    (conjugationLiftHom_eq ρ γ H hγ x h hh)

theorem conjugationLiftEquiv_compatible (hγ : Function.Injective γ)
    (hs : Function.Surjective (conjugationLiftHom ρ γ H hγ))
    (hc : Nat.card G = Nat.card H) (g : G) :
    ConjugationCompatible ρ γ H g (conjugationLiftEquiv ρ γ H hγ hs hc g) := by
  have ht := (Atlas.GroupTheory.subgroup_eq_top_and_bijective_of_surjective_of_card
    (conjugationLiftSubgroup ρ γ H) (conjugationLiftHom ρ γ H hγ) hs hc).1
  have hg : g ∈ conjugationLiftSubgroup ρ γ H := by rw [ht]; trivial
  obtain ⟨h, hh⟩ := hg
  rw [conjugationLiftEquiv_eq ρ γ H hγ hs hc g h hh]
  exact hh

end Finite
end Atlas.LinearAlgebra
