import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! Source-only weighted version of the existing actual root-inversion descent.
The weight is an explicit function on root labels, invariant under simple
reflections. No word-weight formula is assumed. Uncompiled and unaudited. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.WeightedRootInversions
open Classical RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (μ : ι → ℕ)

/-- A sum over the actual positive roots made negative by the actual permutation. -/
def weightedInversions (w : P.weylGroupToPerm.range) : ℕ :=
  ∑ β ∈ rootInversions P b w, μ β

@[simp] theorem weightedInversions_one : weightedInversions P b μ 1 = 0 := by
  simp [weightedInversions, rootInversions]

/-- The same reflection that gives the existing erased-cardinality equality
also preserves the weighted sum. Its membership argument is explicit here;
the private helper in RootInversionLength is not used. -/
theorem erased_weightedInversions_mul_simple
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (w : P.weylGroupToPerm.range) (i : b.support) :
    (∑ β ∈ (rootInversions P b (w * simpleWeylReflection P b i)).erase i.val, μ β) =
      ∑ β ∈ (rootInversions P b w).erase i.val, μ β := by
  apply Finset.sum_equiv (P.reflectionPerm i.val)
  · intro β
    simp only [Finset.mem_erase, mem_rootInversions]
    constructor
    · rintro ⟨hne, hpos, hneg⟩
      have hne' : P.reflectionPerm i.val β ≠ i.val := by
        intro he
        have hβ : β = P.reflectionPerm i.val i.val := by
          calc
            β = P.reflectionPerm i.val (P.reflectionPerm i.val β) :=
              (P.reflectionPerm_self i.val β).symm
            _ = P.reflectionPerm i.val i.val := congrArg (P.reflectionPerm i.val) he
        exact not_isPos_reflection_simple P b i (hβ ▸ hpos)
      refine ⟨hne', hpos.reflectionPerm i.property hne, ?_⟩
      change ¬ b.IsPos (w.val (P.reflectionPerm i.val β)) at hneg
      exact hneg
    · rintro ⟨hne, hpos, hneg⟩
      have hβpos : b.IsPos β := by
        simpa only [P.reflectionPerm_self] using hpos.reflectionPerm i.property hne
      have hβne : β ≠ i.val := by
        intro he
        exact not_isPos_reflection_simple P b i (he ▸ hpos)
      refine ⟨hβne, hβpos, ?_⟩
      change ¬ b.IsPos (w.val (P.reflectionPerm i.val β))
      exact hneg
  · intro β _
    exact (hμ i β).symm

theorem weightedInversions_mul_simple_of_positive
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (w : P.weylGroupToPerm.range) (i : b.support)
    (hpos : b.IsPos (w.val i.val)) :
    weightedInversions P b μ (w * simpleWeylReflection P b i) =
      weightedInversions P b μ w + μ i.val := by
  have hnot : i.val ∉ rootInversions P b w := by
    rw [mem_rootInversions]
    exact fun h => h.2 hpos
  have hmem : i.val ∈ rootInversions P b (w * simpleWeylReflection P b i) := by
    rw [mem_rootInversions]
    refine ⟨b.isPos_of_mem_support i.property, ?_⟩
    intro h
    exact ((simpleWeylReflection_sign_flip P b w i).mp h) hpos
  calc
    weightedInversions P b μ (w * simpleWeylReflection P b i) =
        (∑ β ∈ (rootInversions P b (w * simpleWeylReflection P b i)).erase i.val, μ β) +
          μ i.val := (Finset.sum_erase_add _ μ hmem).symm
    _ = (∑ β ∈ (rootInversions P b w).erase i.val, μ β) + μ i.val := by
      rw [erased_weightedInversions_mul_simple P b μ hμ]
    _ = weightedInversions P b μ w + μ i.val := by
      rw [Finset.erase_eq_of_notMem hnot]
      rfl

theorem weightedInversions_mul_simple_of_negative
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (w : P.weylGroupToPerm.range) (i : b.support)
    (hneg : ¬ b.IsPos (w.val i.val)) :
    weightedInversions P b μ (w * simpleWeylReflection P b i) + μ i.val =
      weightedInversions P b μ w := by
  have hpos := (simpleWeylReflection_sign_flip P b w i).mpr hneg
  simpa only [mul_assoc, simpleWeylReflection_mul_self, mul_one] using
    (weightedInversions_mul_simple_of_positive P b μ hμ
      (w * simpleWeylReflection P b i) i hpos).symm

end Atlas.Chevalley.TwistedE6.WeightedRootInversions
