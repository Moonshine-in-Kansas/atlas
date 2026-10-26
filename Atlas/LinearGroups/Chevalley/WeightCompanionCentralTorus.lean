import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder
import Atlas.LinearGroups.Chevalley.WeightRootCharacterDescent
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusKernel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
/-! Actual torus projection-kernel identification. No full-kernel claim. -/
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


/-- Compatibility of the literal finite-product parameter maps with rho. -/
theorem weightCompanionRho_torusParameters (t : b.support → Rˣ) :
    weightCompanionRho P b O hclosed hmin R
      (weightCompanionTorusParameters P b O hclosed hmin R t) =
        adjointTorusParameters P b R t :=
  weightCompanionTorusProduct_adjoint P b O hclosed hmin R Finset.univ t

/-- Restrict actual torus parameters to the actual projection-kernel intersection. -/
def weightCompanionCentralTorusHom : (adjointTorusParameters P b R).ker →*
    ↥(weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
      (weightCompanionRho P b O hclosed hmin R).ker) where
  toFun t := ⟨weightCompanionTorusParameters P b O hclosed hmin R t.val,
    weightCompanionTorusProduct_mem P b O hclosed hmin R Finset.univ t.val, by
      change weightCompanionRho P b O hclosed hmin R
        (weightCompanionTorusParameters P b O hclosed hmin R t.val)=1
      rw [weightCompanionRho_torusParameters]
      exact t.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' t s := Subtype.ext (map_mul _ t.val s.val)

theorem weightCompanionCentralTorusHom_bijective
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    Function.Bijective (weightCompanionCentralTorusHom P b O hclosed hmin R) := by
  constructor
  · intro t s h
    apply Subtype.ext
    apply weightCompanionTorusParameters_injective_of_span P b O hclosed hmin R hspan
    exact congrArg Subtype.val h
  · intro g
    have hg := (le_of_eq (weightCompanionTorusSubgroup_eq_range P b O hclosed hmin R)) g.property.1
    obtain ⟨t,ht⟩ := hg
    have hk : adjointTorusParameters P b R t=1 := by
      rw [← weightCompanionRho_torusParameters P b O hclosed hmin R t, ht]
      exact g.property.2
    exact ⟨⟨t,hk⟩,Subtype.ext ht⟩

/-- The literal central torus subgroup is the adjoint parameter kernel. -/
def weightCompanionCentralTorusEquiv
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    (adjointTorusParameters P b R).ker ≃*
      ↥(weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
        (weightCompanionRho P b O hclosed hmin R).ker) :=
  MulEquiv.ofBijective (weightCompanionCentralTorusHom P b O hclosed hmin R)
    (weightCompanionCentralTorusHom_bijective P b O hclosed hmin R hspan)

/-- Actual central torus character description, without identifying the full kernel. -/
def weightCompanionCentralTorusCharacterEquiv
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    ↥(weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
      (weightCompanionRho P b O hclosed hmin R).ker) ≃*
        (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) :=
  (weightCompanionCentralTorusEquiv P b O hclosed hmin R hspan).symm.trans
    (adjointTorusKernelCharacterEquiv P R b)

theorem weightCompanionCentralTorus_card
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    Nat.card ↥(weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
      (weightCompanionRho P b O hclosed hmin R).ker) =
        Nat.card (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) :=
  Nat.card_congr (weightCompanionCentralTorusCharacterEquiv P b O hclosed hmin R hspan).toEquiv
end Atlas.Chevalley
