import Atlas.LinearGroups.Chevalley.WeightCompanionTorusFaithful
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusKernel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
/-! Literal companion torus range and finite-field order.
This is the torus order, not the full group's order or center. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem weightCompanionTorusParameters_single (i : b.support) (a : Rˣ) :
    weightCompanionTorusParameters P b O hclosed hmin R (Pi.mulSingle i a) =
      weightCompanionTorus P b O hclosed hmin R i a := by
  have hs (s : Finset b.support) :
      weightCompanionTorusProduct P b O hclosed hmin R s (Pi.mulSingle i a) =
        if i ∈ s then weightCompanionTorus P b O hclosed hmin R i a else 1 := by
    induction s using Finset.induction_on with
    | empty => simp [weightCompanionTorusProduct]
    | @insert j s hj ih =>
      unfold weightCompanionTorusProduct
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj]
      unfold weightCompanionTorusProduct at ih
      rw [ih]
      by_cases hji : j=i
      · subst j
        simp [Pi.mulSingle_apply,hj]
      · simp [Pi.mulSingle_apply,hji,Ne.symm hji,weightCompanionTorus]
  exact (hs Finset.univ).trans (by simp)

theorem weightCompanionTorusProduct_mem (s : Finset b.support) (t : b.support → Rˣ) :
    weightCompanionTorusProduct P b O hclosed hmin R s t ∈
      weightCompanionTorusSubgroup P b O hclosed hmin R := by
  apply Finset.noncommProd_induction
  · intro g h hg hh
    exact (weightCompanionTorusSubgroup P b O hclosed hmin R).mul_mem hg hh
  · exact (weightCompanionTorusSubgroup P b O hclosed hmin R).one_mem
  · intro i hi
    exact Subgroup.subset_closure ⟨i,t i,rfl⟩

theorem weightCompanionTorusSubgroup_eq_range :
    weightCompanionTorusSubgroup P b O hclosed hmin R =
      (weightCompanionTorusParameters P b O hclosed hmin R).range := by
  apply le_antisymm
  · rw [weightCompanionTorusSubgroup,Subgroup.closure_le]
    rintro g ⟨i,a,rfl⟩
    exact ⟨Pi.mulSingle i a,weightCompanionTorusParameters_single P b O hclosed hmin R i a⟩
  · rintro g ⟨t,rfl⟩
    exact weightCompanionTorusProduct_mem P b O hclosed hmin R Finset.univ t

/-- An explicit isomorphism with the actual generated torus, from integral spanning. -/
def weightCompanionTorusParametersEquiv
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    (b.support → Rˣ) ≃* weightCompanionTorusSubgroup P b O hclosed hmin R :=
  (MonoidHom.ofInjective (weightCompanionTorusParameters_injective_of_span
    P b O hclosed hmin R hspan)).trans
      (MulEquiv.subgroupCongr (weightCompanionTorusSubgroup_eq_range P b O hclosed hmin R).symm)

theorem weightCompanionTorus_card
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    Nat.card (weightCompanionTorusSubgroup P b O hclosed hmin R) =
      Nat.card Rˣ ^ Nat.card b.support := by
  rw [← Nat.card_congr (weightCompanionTorusParametersEquiv P b O hclosed hmin R hspan).toEquiv,
    Nat.card_fun]

variable (K : Type*) [Field K] [Fintype K]
theorem weightCompanionTorus_card_finiteField
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    Nat.card (weightCompanionTorusSubgroup P b O hclosed hmin K) =
      (Fintype.card K - 1) ^ Nat.card b.support := by
  rw [weightCompanionTorus_card P b O hclosed hmin K hspan,
    Nat.card_units,Nat.card_eq_fintype_card]
end Atlas.Chevalley
