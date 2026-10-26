import Atlas.LinearGroups.Chevalley.RootData.SupportedRootWordLabels
import Atlas.LinearGroups.Chevalley.RootData.RootWeylLongest

/-! Positivity on a selected simple support implies positivity on every
positive root supported there. The existing nonnegative-coordinate argument
is reused through the actual longest Weyl element's sign reversal. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- No root enumeration, parabolic minimality, or group-order assumption is
required. The support and positivity are those of the original actual base. -/
theorem rootWeyl_isPos_of_simple_support
    (S : Finset b.support) (w : P.weylGroupToPerm.range)
    (hw : ∀ i ∈ S, b.IsPos (w.val i.val))
    {β : ι} (hβ : b.IsPos β)
    (hs : (rootSimpleCoefficients P b β).support ⊆ S) :
    b.IsPos (w.val β) := by
  have hsimple : ∀ i ∈ S,
      ¬ b.IsPos ((rootWeylLongest P b * w).val i.val) := by
    intro i hi
    change ¬ b.IsPos ((rootWeylLongest P b).val (w.val i.val))
    exact rootWeylLongest_not_isPos P b (hw i hi)
  have hnegative := rootWeyl_not_isPos_of_simple_support P b S
    (rootWeylLongest P b * w) hsimple hβ hs
  change ¬ b.IsPos ((rootWeylLongest P b).val (w.val β)) at hnegative
  by_contra hn
  exact hnegative ((rootWeylLongest_isPos_iff P b (w.val β)).mpr hn)

end Atlas.Chevalley.RootData
