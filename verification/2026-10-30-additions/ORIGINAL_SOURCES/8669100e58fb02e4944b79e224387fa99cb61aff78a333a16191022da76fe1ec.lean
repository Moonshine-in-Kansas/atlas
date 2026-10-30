import FamilyWork.WeightedParabolicFactor

/-! Transport of actual weighted inversion statistics along a marked Weyl map.
Both preservation of reduced-word length and equality of the simple-root
weights are explicit. Ordinary length preservation alone is not enough. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.WeightedWeylTransport
open Classical RootData WeightedRootInversions WeightedParabolicFactor

variable {ι M N ι' M' N' : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (μ : ι → ℕ)
  (Q : RootPairing ι' ℤ M' N') [Q.IsCrystallographic] [Q.IsReduced]
  (c : Q.Base) (ν : ι' → ℕ)

/-- Choose an actual shortest source word. Its mapped word is still reduced,
and each of its letters contributes the same actual root weight. -/
theorem weightedInversions_transport
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (hν : ∀ i : c.support, ∀ β : ι', ν (Q.reflectionPerm i.val β) = ν β)
    (f : P.weylGroupToPerm.range → Q.weylGroupToPerm.range)
    (k : b.support → c.support)
    (hword : ∀ l, f (rootWeylWord P b l) = rootWeylWord Q c (l.map k))
    (hlen : ∀ w, rootWeylLength Q c (f w) = rootWeylLength P b w)
    (hweight : ∀ i : b.support, ν (k i).val = μ i.val)
    (w : P.weylGroupToPerm.range) :
    weightedInversions Q c ν (f w) = weightedInversions P b μ w := by
  obtain ⟨l, hl, hlw⟩ := rootWeylLength_spec P b w
  have he : rootWeylWord P b l = w := by
    apply Subtype.ext
    simpa only [rootWeylWord_val] using hlw
  have hred : IsReducedRootWord P b l := by
    change rootWeylLength P b (rootWeylWord P b l) = l.length
    rw [he]
    exact hl.symm
  have hred' : IsReducedRootWord Q c (l.map k) := by
    change rootWeylLength Q c (rootWeylWord Q c (l.map k)) = (l.map k).length
    rw [← hword, he, hlen, List.length_map]
    exact hl.symm
  calc
    weightedInversions Q c ν (f w) =
        weightedInversions Q c ν (rootWeylWord Q c (l.map k)) := by
      rw [← hword, he]
    _ = ((l.map k).map (fun i => ν i.val)).sum :=
      weightedInversions_reduced_word Q c ν hν (l.map k) hred'
    _ = (l.map (fun i => μ i.val)).sum := by
      simp only [List.map_map, Function.comp_def, hweight]
    _ = weightedInversions P b μ w := by
      rw [← he, weightedInversions_reduced_word P b μ hμ l hred]

end Atlas.Chevalley.TwistedE6.WeightedWeylTransport
