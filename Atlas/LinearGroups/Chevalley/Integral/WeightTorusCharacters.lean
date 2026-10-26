import Atlas.LinearGroups.Chevalley.Integral.WeightCoordinates
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-! Actual weight characters distinguish coroot parameters.
Spanning is a literal integral-lattice condition, not a group faithfulness premise. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base)
  (R : Type*) [CommRing R]

def weightTorusCharacter (t : b.support → Rˣ) (μ : WeightLattice P) : Rˣ :=
  ∏ i : b.support, (t i) ^ μ (corootBasis P b i)

@[simp] theorem weightTorusCharacter_fundamental (t : b.support → Rˣ) (j : b.support) :
    weightTorusCharacter P b R t (fundamentalWeights P b j) = t j := by
  simp [weightTorusCharacter, fundamentalWeights_pairing]

/-- The weights on which this parameter tuple acts trivially form an integral submodule. -/
def weightTorusCharacterKernel (t : b.support → Rˣ) : Submodule ℤ (WeightLattice P) where
  carrier := {μ | weightTorusCharacter P b R t μ=1}
  zero_mem' := by simp [weightTorusCharacter]
  add_mem' := by
    intro μ ν hμ hν
    change weightTorusCharacter P b R t (μ+ν)=1
    simp only [weightTorusCharacter, LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib]
    change weightTorusCharacter P b R t μ * weightTorusCharacter P b R t ν = 1
    rw [hμ,hν,one_mul]
  smul_mem' := by
    intro n μ hμ
    change weightTorusCharacter P b R t (n • μ)=1
    have he : weightTorusCharacter P b R t (n • μ) =
        weightTorusCharacter P b R t μ ^ n := by
      simp only [weightTorusCharacter, LinearMap.smul_apply, smul_eq_mul,
        mul_comm n, zpow_mul, Finset.prod_zpow]
    rw [he,hμ,one_zpow]

/-- A tuple acting trivially on a spanning set is literally the identity tuple. -/
theorem weightTorusParameters_eq_one_of_spanning (T : Set (WeightLattice P))
    (hspan : Submodule.span ℤ T=⊤) (t : b.support → Rˣ)
    (ht : ∀ μ ∈ T, weightTorusCharacter P b R t μ=1) : t=1 := by
  have hk : Submodule.span ℤ T ≤ weightTorusCharacterKernel P b R t :=
    Submodule.span_le.mpr ht
  rw [hspan] at hk
  funext i
  have hi := hk (Submodule.mem_top : fundamentalWeights P b i ∈ (⊤ : Submodule ℤ (WeightLattice P)))
  change weightTorusCharacter P b R t (fundamentalWeights P b i)=1 at hi
  simpa using hi

/-- Exact useful form for the adjoint plus selected minuscule blocks. -/
theorem weightTorusParameters_eq_one_of_root_and_weight_span
    (T : Set (WeightLattice P))
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ T)=⊤)
    (t : b.support → Rˣ)
    (hr : ∀ a, weightTorusCharacter P b R t (rootWeight P a)=1)
    (hw : ∀ μ ∈ T, weightTorusCharacter P b R t μ=1) : t=1 := by
  apply weightTorusParameters_eq_one_of_spanning P b R _ hspan t
  rintro μ (⟨a,rfl⟩ | hμ)
  · exact hr a
  · exact hw μ hμ
end Atlas.Chevalley.Integral.Minuscule
