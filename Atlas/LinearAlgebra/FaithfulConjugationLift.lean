import Atlas.LinearAlgebra.ConjugationLiftSubgroup

/-! A faithful linear representation of the target transports the compatible
lift homomorphism back to the target's actual carrier. This includes concrete
matrix-unit groups, without replacing their carrier by a recognized group. -/
noncomputable section
namespace Atlas.LinearAlgebra
variable {R V A G K : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Ring A] [Module R A] [Group G] [Group K]
variable (ρ : G →* A) (γ : V →ₗ[R] A) (σ : K →* (V ≃ₗ[R] V))

def faithfulConjugationLiftHom (hγ : Function.Injective γ)
    (hσ : Function.Injective σ) :
    conjugationLiftSubgroup ρ γ σ.range →* K :=
  (MonoidHom.ofInjective hσ).symm.toMonoidHom.comp
    (conjugationLiftHom ρ γ σ.range hγ)

theorem faithfulConjugationLiftHom_compatible (hγ : Function.Injective γ)
    (hσ : Function.Injective σ) (g : conjugationLiftSubgroup ρ γ σ.range) (v : V) :
    ρ g.val * γ v * ρ g.val⁻¹ =
      γ (σ (faithfulConjugationLiftHom ρ γ σ hγ hσ g) v) := by
  change _ = γ (σ ((MonoidHom.ofInjective hσ).symm
    (conjugationLiftHom ρ γ σ.range hγ g)) v)
  rw [MonoidHom.apply_ofInjective_symm]
  exact conjugationLiftHom_compatible ρ γ σ.range hγ g v

theorem faithfulConjugationLiftHom_eq (hγ : Function.Injective γ)
    (hσ : Function.Injective σ) (g : conjugationLiftSubgroup ρ γ σ.range)
    (k : K) (hk : ∀ v, ρ g.val * γ v * ρ g.val⁻¹ = γ (σ k v)) :
    faithfulConjugationLiftHom ρ γ σ hγ hσ g = k := by
  apply (MonoidHom.ofInjective hσ).injective
  change (MonoidHom.ofInjective hσ) ((MonoidHom.ofInjective hσ).symm
    (conjugationLiftHom ρ γ σ.range hγ g)) = (MonoidHom.ofInjective hσ) k
  rw [MulEquiv.apply_symm_apply]
  exact conjugationLiftHom_eq ρ γ σ.range hγ g
    ⟨σ k, ⟨k, rfl⟩⟩ hk

/-- Only actual generator lifts are needed; all target elements then lie in
the range of the already constructed compatible-lift homomorphism. -/
theorem faithfulConjugationLiftHom_surjective_of_generators
    (hγ : Function.Injective γ) (hσ : Function.Injective σ)
    (S : Set K) (hS : Subgroup.closure S = ⊤)
    (hex : ∀ k ∈ S, ∃ g : G, ∀ v, ρ g * γ v * ρ g⁻¹ = γ (σ k v)) :
    Function.Surjective (faithfulConjugationLiftHom ρ γ σ hγ hσ) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hS]
  apply (Subgroup.closure_le _).mpr
  intro k hk
  obtain ⟨g, hg⟩ := hex k hk
  let x : conjugationLiftSubgroup ρ γ σ.range := ⟨g, ⟨σ k, ⟨k, rfl⟩⟩, hg⟩
  exact ⟨x, faithfulConjugationLiftHom_eq ρ γ σ hγ hσ x k hg⟩

section Finite
variable [Finite G]

/-- This is the equivalence of the original group carriers. The sole
cardinality input is independent equality of their finite orders. -/
def faithfulConjugationLiftEquiv (hγ : Function.Injective γ)
    (hσ : Function.Injective σ)
    (hs : Function.Surjective (faithfulConjugationLiftHom ρ γ σ hγ hσ))
    (hc : Nat.card G = Nat.card K) : G ≃* K :=
  Atlas.GroupTheory.subgroupSurjectionEquiv (conjugationLiftSubgroup ρ γ σ.range)
    (faithfulConjugationLiftHom ρ γ σ hγ hσ) hs hc

theorem faithfulConjugationLiftEquiv_eq (hγ : Function.Injective γ)
    (hσ : Function.Injective σ)
    (hs : Function.Surjective (faithfulConjugationLiftHom ρ γ σ hγ hσ))
    (hc : Nat.card G = Nat.card K) (g : G) (k : K)
    (hk : ∀ v, ρ g * γ v * ρ g⁻¹ = γ (σ k v)) :
    faithfulConjugationLiftEquiv ρ γ σ hγ hσ hs hc g = k := by
  let x : conjugationLiftSubgroup ρ γ σ.range := ⟨g, ⟨σ k, ⟨k, rfl⟩⟩, hk⟩
  exact (Atlas.GroupTheory.subgroupSurjectionEquiv_apply
    (conjugationLiftSubgroup ρ γ σ.range)
    (faithfulConjugationLiftHom ρ γ σ hγ hσ) hs hc x).trans
    (faithfulConjugationLiftHom_eq ρ γ σ hγ hσ x k hk)

end Finite
end Atlas.LinearAlgebra
