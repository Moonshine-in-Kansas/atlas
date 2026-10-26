import Atlas.LinearGroups.Chevalley.WeightCompanionTorusParameters
import Atlas.LinearGroups.Chevalley.Integral.WeightTorusCharacters
/-! Faithfulness of the actual tuple map from integral weight spanning. -/
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

theorem weightCompanionTorusParameters_kernel_trivial_of_span
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤)
    (t : b.support → Rˣ)
    (ht : weightCompanionTorusParameters P b O hclosed hmin R t=1) : t=1 := by
  apply weightTorusParameters_eq_one_of_root_and_weight_span P b R _ hspan t
  · intro a
    have ha := congrArg (fun g : WeightCompanion P b O hclosed hmin R => g.val.1) ht
    change (weightCompanionTorusProduct P b O hclosed hmin R Finset.univ t).val.1=1 at ha
    rw [weightCompanionTorusProduct_adjoint] at ha
    have he := (adjointTorusParameters_eq_one_iff P b R t).mp ha a
    have hp (i : b.support) : (rootWeight P a) (corootBasis P b i)=P.pairingIn ℤ a i := by
      rw [← weightCoordinates_apply, rootWeight_coordinates]
      exact (P.algebraMap_pairingIn ℤ a i).symm
    simpa only [weightTorusCharacter,hp] using he
  · rintro μ ⟨k,hμ⟩
    have hb := congrArg (fun g : WeightCompanion P b O hclosed hmin R => (g.val.2 k).val) ht
    change ((weightCompanionTorusProduct P b O hclosed hmin R Finset.univ t).val.2 k).val=1 at hb
    rw [weightCompanionTorusProduct_minuscule] at hb
    have hc := congrArg (fun A => A ⟨μ,hμ⟩ ⟨μ,hμ⟩) hb
    have hbase (i : b.support) : corootBasis P b i=corootElement P i.val := by
      apply Subtype.ext
      exact b.flip.coe_toWeightBasisInt_apply (⟨i.val,i.property⟩ : b.flip.support)
    apply Units.ext
    simpa [weightTorusCharacter,hbase,map_prod] using hc

theorem weightCompanionTorusParameters_injective_of_span
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k})=⊤) :
    Function.Injective (weightCompanionTorusParameters P b O hclosed hmin R) := by
  intro t v h
  have hh : weightCompanionTorusParameters P b O hclosed hmin R (t*v⁻¹)=1 := by
    rw [map_mul,map_inv,h,mul_inv_cancel]
  have hv := weightCompanionTorusParameters_kernel_trivial_of_span P b O hclosed hmin R hspan _ hh
  exact mul_inv_eq_one.mp hv
end Atlas.Chevalley
