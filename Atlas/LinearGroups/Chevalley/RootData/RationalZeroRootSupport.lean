import Atlas.LinearGroups.Chevalley.RootData.RationalRootWeylLinear

/-! A dominant rational functional cuts out exactly the standard root subsystem
supported on its zero-valued simple directions. Positive and negative roots
are both included; no orientation of a chosen pair is assumed. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Actual simple directions on which the rational functional vanishes. -/
def rationalZeroSimpleSet (f : (b.support → ℚ) →ₗ[ℚ] ℚ) : Finset b.support :=
  Finset.univ.filter (fun i => f (rationalRootCoordinates P b i.val) = 0)

private theorem rootSimpleCoefficients_opposite (β : ι) :
    rootSimpleCoefficients P b (P.reflectionPerm β β) =
      -rootSimpleCoefficients P b β := by
  simp only [rootSimpleCoefficients, P.rootSpanMem_reflectionPerm_self, map_neg]

/-- The support criterion holds for every root, including the negative roots. -/
theorem rationalRoot_functional_eq_zero_iff_support
    (f : (b.support → ℚ) →ₗ[ℚ] ℚ)
    (hf : ∀ i : b.support, 0 ≤ f (rationalRootCoordinates P b i.val)) (β : ι) :
    f (rationalRootCoordinates P b β) = 0 ↔
      ∀ i ∈ (rootSimpleCoefficients P b β).support,
        f (rationalRootCoordinates P b i.val) = 0 := by
  have hp (γ : ι) (hγ : b.IsPos γ) :
      f (rationalRootCoordinates P b γ) = 0 ↔
        ∀ i ∈ (rootSimpleCoefficients P b γ).support,
          f (rationalRootCoordinates P b i.val) = 0 := by
    exact positiveRoot_functional_eq_zero_iff_support P b
      (f.toAddMonoidHom.comp (rationalRootSpanMap P b).toAddMonoidHom) hf hγ
  rcases RootPairing.Base.IsPos.or_neg b β with hpos | hneg
  · exact hp β hpos
  · have hn : b.IsPos (P.reflectionPerm β β) := hneg
    have hz := hp (P.reflectionPerm β β) hn
    simpa only [rationalRootCoordinates_opposite, map_neg, neg_eq_zero,
      rootSimpleCoefficients_opposite, Finsupp.support_neg] using hz

theorem rationalRoot_mem_zeroSimpleSpan_iff_support
    (f : (b.support → ℚ) →ₗ[ℚ] ℚ) (β : ι) :
    rationalRootCoordinates P b β ∈
        Pi.spanSubset ℚ (rationalZeroSimpleSet P b f : Set b.support) ↔
      ∀ i ∈ (rootSimpleCoefficients P b β).support,
        f (rationalRootCoordinates P b i.val) = 0 := by
  simp only [Pi.mem_spanSubset_iff, rationalZeroSimpleSet, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and, rationalRootCoordinates_coefficient,
    Int.cast_eq_zero, Finsupp.mem_support_iff]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h i hn)
  · intro h i hi
    by_contra hn
    exact hi (h i hn)

/-- For a dominant rational functional, its zero roots are exactly the roots
in the coordinate span of its zero-valued simple directions. -/
theorem rationalRoot_functional_eq_zero_iff_mem_zeroSimpleSpan
    (f : (b.support → ℚ) →ₗ[ℚ] ℚ)
    (hf : ∀ i : b.support, 0 ≤ f (rationalRootCoordinates P b i.val)) (β : ι) :
    f (rationalRootCoordinates P b β) = 0 ↔
      rationalRootCoordinates P b β ∈
        Pi.spanSubset ℚ (rationalZeroSimpleSet P b f : Set b.support) :=
  (rationalRoot_functional_eq_zero_iff_support P b f hf β).trans
    (rationalRoot_mem_zeroSimpleSpan_iff_support P b f β).symm

theorem rationalZeroSimpleSpan_le_ker (f : (b.support → ℚ) →ₗ[ℚ] ℚ) :
    Pi.spanSubset ℚ (rationalZeroSimpleSet P b f : Set b.support) ≤ LinearMap.ker f := by
  rw [Pi.spanSubset, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  change f (Pi.basisFun ℚ b.support i) = 0
  rw [← rationalRootCoordinates_simple_eq_basis P b i]
  exact (Finset.mem_filter.mp hi).2

end Atlas.Chevalley.RootData
