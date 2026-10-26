import Atlas.LinearGroups.Chevalley.PositiveRootCanonicalFamily
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootHeightEnumeration
import Atlas.LinearGroups.Chevalley.PositiveRootProductInjective

/-! A concrete injective positive-root parameter map into the existing U.
Surjectivity, closure of its image, and collection are separate obligations. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- Every listed product belongs to the original all-witness subgroup,
independently of root coherence or of the order of the list. -/
theorem positiveRootLiftProduct_mem_witnessed
    (L : ∀ β : {β : ι // b.IsPos β}, WeightCompanionRootLift P b O hc hm R β.val)
    (l : List {β : ι // b.IsPos β}) (s : {β : ι // b.IsPos β} → R) :
    positiveRootLiftProduct P b R O hc hm L l s ∈
      positiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  induction l with
  | nil => exact (positiveWitnessedWeightCompanionSubgroup P b O hc hm R).one_mem
  | cons β l ih =>
    change weightCompanionRootLiftHom P b O hc hm R (L β) (Multiplicative.ofAdd (s β)) *
      positiveRootLiftProduct P b R O hc hm L l s ∈ _
    exact (positiveWitnessedWeightCompanionSubgroup P b O hc hm R).mul_mem
      (rootLiftHom_mem_positiveWitnessedWeightCompanionSubgroup P b O hc hm R
        β.property (L β) (Multiplicative.ofAdd (s β))) ih

/-- The fixed height-ordered product, with codomain restricted to the actual U.
It is a parameter map, not a homomorphism from an additive direct product. -/
def positiveRootChosenProduct (s : {β : ι // b.IsPos β} → R) :
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
  ⟨positiveRootLiftProduct P b R O hc hm (positiveRootChosenLift P b O hc hm R)
      (positiveRootHeightList P b) s,
    positiveRootLiftProduct_mem_witnessed P b O hc hm R
      (positiveRootChosenLift P b O hc hm R) (positiveRootHeightList P b) s⟩

theorem positiveRootChosenProduct_val (s : {β : ι // b.IsPos β} → R) :
    (positiveRootChosenProduct P b O hc hm R s).val =
      positiveRootLiftProduct P b R O hc hm (positiveRootChosenLift P b O hc hm R)
        (positiveRootHeightList P b) s := rfl

/-- Parameters remain distinguishable after the actual adjoint projection.
This does not assert that the whole companion projection is injective. -/
theorem positiveRootChosenProduct_adjoint_injective :
    Function.Injective (fun s : {β : ι // b.IsPos β} → R =>
      weightCompanionRho P b O hc hm R (positiveRootChosenProduct P b O hc hm R s).val) :=
  positiveRootLiftProduct_adjoint_injective P b R O hc hm
    (positiveRootChosenLift P b O hc hm R) (positiveRootHeightList P b)
    (positiveRootHeightList_nodup P b) (positiveRootHeightList_pairwise P b)
    (mem_positiveRootHeightList P b)

theorem positiveRootChosenProduct_injective :
    Function.Injective (positiveRootChosenProduct P b O hc hm R) := by
  intro s t h
  apply positiveRootChosenProduct_adjoint_injective P b O hc hm R
  exact congrArg (fun g : positiveWitnessedWeightCompanionSubgroup P b O hc hm R =>
    weightCompanionRho P b O hc hm R g.val) h

/-- Finite positive-root coordinates inject into the existing U. This
embedding is not asserted to be onto. -/
def positiveRootChosenProductEmbedding :
    ({β : ι // b.IsPos β} → R) ↪ positiveWitnessedWeightCompanionSubgroup P b O hc hm R where
  toFun := positiveRootChosenProduct P b O hc hm R
  inj' := positiveRootChosenProduct_injective P b O hc hm R

end Atlas.Chevalley
