import Atlas.LinearGroups.Chevalley.RootData.RootWeylLongest
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! Length complements and common reduced extensions in the actual Weyl image. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Left multiplication by the longest element complements the inversion set. -/
theorem rootWeylLength_longest_mul_add (w : P.weylGroupToPerm.range) :
    rootWeylLength P b (rootWeylLongest P b * w) + rootWeylLength P b w =
      (Finset.univ.filter (fun β : ι => b.IsPos β)).card := by
  have hleft : rootInversions P b (rootWeylLongest P b * w) =
      (Finset.univ.filter (fun β : ι => b.IsPos β)).filter
        (fun β => b.IsPos (w.val β)) := by
    ext β
    simp only [mem_rootInversions, Finset.mem_filter, Finset.mem_univ, true_and]
    change (b.IsPos β ∧ ¬ b.IsPos ((rootWeylLongest P b).val (w.val β))) ↔ _
    rw [rootWeylLongest_isPos_iff, not_not]
  have hright : rootInversions P b w =
      (Finset.univ.filter (fun β : ι => b.IsPos β)).filter
        (fun β => ¬ b.IsPos (w.val β)) := by
    ext β
    simp only [mem_rootInversions, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← rootInversionCount_eq_rootWeylLength P b (rootWeylLongest P b * w),
    ← rootInversionCount_eq_rootWeylLength P b w]
  simp only [rootInversionCount, hleft, hright]
  exact Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun β : ι => b.IsPos β)) (fun β => b.IsPos (w.val β))

/-- The quotient from any actual Weyl element to the longest one has
complementary length. -/
theorem rootWeylLength_inv_mul_longest_add (w : P.weylGroupToPerm.range) :
    rootWeylLength P b (w⁻¹ * rootWeylLongest P b) + rootWeylLength P b w =
      (Finset.univ.filter (fun β : ι => b.IsPos β)).card := by
  have hinv : rootWeylLength P b (w⁻¹ * rootWeylLongest P b) =
      rootWeylLength P b (rootWeylLongest P b * w) := by
    simpa only [mul_inv_rev, rootWeylLongest_inv] using
      rootWeylLength_inv P b (rootWeylLongest P b * w)
  rw [hinv]
  exact rootWeylLength_longest_mul_add P b w

/-- Every actual reduced word extends, as a prefix, to a reduced word for
the same longest Weyl element. -/
theorem exists_reduced_append_to_longest (l : List b.support)
    (hl : IsReducedRootWord P b l) :
    ∃ r : List b.support,
      rootWeylWord P b (l ++ r) = rootWeylLongest P b ∧
        IsReducedRootWord P b (l ++ r) := by
  obtain ⟨r, hrlen, hr⟩ := rootWeylLength_spec P b
    ((rootWeylWord P b l)⁻¹ * rootWeylLongest P b)
  have hrv : rootWeylWord P b r =
      (rootWeylWord P b l)⁻¹ * rootWeylLongest P b := by
    apply Subtype.ext
    simpa only [rootWeylWord_val] using hr
  have hword : rootWeylWord P b (l ++ r) = rootWeylLongest P b := by
    rw [rootWeylWord_append, hrv, mul_inv_cancel_left]
  refine ⟨r, hword, ?_⟩
  change rootWeylLength P b (rootWeylWord P b (l ++ r)) = (l ++ r).length
  rw [hword, rootWeylLength_longest, List.length_append, hrlen]
  have hc := rootWeylLength_inv_mul_longest_add P b (rootWeylWord P b l)
  change rootWeylLength P b (rootWeylWord P b l) = l.length at hl
  omega

/-- Two reduced prefixes admit reduced extensions representing the same
actual Weyl element. -/
theorem exists_common_reduced_extensions (l r : List b.support)
    (hl : IsReducedRootWord P b l) (hr : IsReducedRootWord P b r) :
    ∃ l' r' : List b.support,
      IsReducedRootWord P b (l ++ l') ∧ IsReducedRootWord P b (r ++ r') ∧
        rootWeylWord P b (l ++ l') = rootWeylWord P b (r ++ r') := by
  obtain ⟨l', hle, hlred⟩ := exists_reduced_append_to_longest P b l hl
  obtain ⟨r', hre, hrred⟩ := exists_reduced_append_to_longest P b r hr
  exact ⟨l', r', hlred, hrred, hle.trans hre.symm⟩

/-- A positive root witnessed at the end of a reduced prefix remains a
marked occurrence in an extension to the longest word. This asserts only
root-word combinatorics, not independence of conjugated root families. -/
theorem exists_reduced_marked_extension (l : List b.support)
    (hl : IsReducedRootWord P b l) (i : b.support)
    (hpos : b.IsPos ((rootWeylWord P b l).val i.val)) :
    ∃ r : List b.support,
      rootWeylWord P b (l ++ i :: r) = rootWeylLongest P b ∧
        IsReducedRootWord P b (l ++ i :: r) := by
  have hs : rootWeylWord P b (l ++ [i]) =
      rootWeylWord P b l * simpleWeylReflection P b i := by
    rw [rootWeylWord_append]
    simp only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
  have hred : IsReducedRootWord P b (l ++ [i]) := by
    change rootWeylLength P b (rootWeylWord P b (l ++ [i])) = (l ++ [i]).length
    rw [hs, rootWeylLength_mul_simple_of_positive P b _ i hpos]
    change rootWeylLength P b (rootWeylWord P b l) = l.length at hl
    rw [hl, List.length_append, List.length_singleton]
  obtain ⟨r, he, hred'⟩ := exists_reduced_append_to_longest P b (l ++ [i]) hred
  exact ⟨r, by simpa only [List.append_assoc, List.singleton_append] using he,
    by simpa only [List.append_assoc, List.singleton_append] using hred'⟩

end Atlas.Chevalley.RootData
