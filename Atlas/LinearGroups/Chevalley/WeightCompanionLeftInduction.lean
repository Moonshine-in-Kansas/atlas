import Atlas.LinearGroups.Chevalley.WeightCompanionRootLaws
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Left-generator induction for the actual companion. Negative parameters
handle inverses, so a predicate need not be closed under arbitrary products
or inversion. This is the existing generated model's literal closure rule. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

theorem weightCompanion_induction_left
    {C : WeightCompanion P b O hc hm R → Prop}
    (hone : C 1)
    (hx : ∀ i t g, C g → C (weightCompanionX P b O hc hm R i t * g))
    (hy : ∀ i t g, C g → C (weightCompanionY P b O hc hm R i t * g))
    (g : WeightCompanion P b O hc hm R) : C g := by
  rcases g with ⟨g,hg⟩
  induction hg using Subgroup.closure_induction_left with
  | one => exact hone
  | mul_left x hxmem y hymem ih =>
    rcases hxmem with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · exact hx i t ⟨y,hymem⟩ ih
    · exact hy i t ⟨y,hymem⟩ ih
  | inv_mul_cancel x hxmem y hymem ih =>
    rcases hxmem with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · change C ((weightCompanionX P b O hc hm R i t)⁻¹ * ⟨y,hymem⟩)
      have hinv : weightCompanionX P b O hc hm R i (-t) =
          (weightCompanionX P b O hc hm R i t)⁻¹ :=
        map_inv (weightCompanionXHom P b O hc hm R i) (Multiplicative.ofAdd t)
      rw [← hinv]
      exact hx i (-t) ⟨y,hymem⟩ ih
    · change C ((weightCompanionY P b O hc hm R i t)⁻¹ * ⟨y,hymem⟩)
      have hinv : weightCompanionY P b O hc hm R i (-t) =
          (weightCompanionY P b O hc hm R i t)⁻¹ :=
        map_inv (weightCompanionYHom P b O hc hm R i) (Multiplicative.ofAdd t)
      rw [← hinv]
      exact hy i (-t) ⟨y,hymem⟩ ih

end Atlas.Chevalley
