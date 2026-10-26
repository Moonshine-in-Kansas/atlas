import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionBraids
import Atlas.LinearGroups.Chevalley.RootData.ReducedEvaluationData
import Atlas.LinearGroups.Chevalley.RootData.TwoDescentSuffixDihedral
import Atlas.LinearGroups.Chevalley.RootData.SimpleCartanCases

/-! The actual common alternating suffix at two distinct descents. The proof
uses the actual Cartan pair, root-sign descents and literal reflection braids;
it does not assume a Coxeter presentation. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Atlas.GroupTheory.ReducedWords
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Rank-two alternating length. Only distinct simple indices are used in
the suffix theorem; the otherwise branch also gives a harmless diagonal value. -/
def simpleBraidLength (i j : b.support) : ℕ :=
  if b.cartanMatrix i j * b.cartanMatrix j i = 0 then 2
  else if b.cartanMatrix i j * b.cartanMatrix j i = 1 then 3
  else if b.cartanMatrix i j * b.cartanMatrix j i = 2 then 4
  else 6

theorem simpleBraidLength_pos (i j : b.support) :
    0 < simpleBraidLength P b i j := by
  unfold simpleBraidLength
  split_ifs <;> omega

theorem simpleBraidLength_symm (i j : b.support) :
    simpleBraidLength P b i j = simpleBraidLength P b j i := by
  simp only [simpleBraidLength, mul_comm]

private theorem commonSuffix_of_words
    (w : P.weylGroupToPerm.range) (a c : List b.support) (n : ℕ)
    (hbraid : rootWeylWord P b a = rootWeylWord P b c)
    (hsq : rootWeylWord P b a * rootWeylWord P b a = 1)
    (hdrop : rootWeylLength P b (w * rootWeylWord P b a) + n =
      rootWeylLength P b w) :
    ∃ v : P.weylGroupToPerm.range,
      rootWeylLength P b v + n = rootWeylLength P b w ∧
      v * wordEval (simpleWeylReflection P b) a = w ∧
      v * wordEval (simpleWeylReflection P b) c = w := by
  refine ⟨w * rootWeylWord P b a, hdrop, ?_, ?_⟩
  · rw [root_wordEval_eq_rootWeylWord, mul_assoc, hsq, mul_one]
  · rw [root_wordEval_eq_rootWeylWord, ← hbraid, mul_assoc, hsq, mul_one]

private theorem commonSuffix_two (w : P.weylGroupToPerm.range)
    (i j : b.support) (hij : b.cartanMatrix i j = 0)
    (hji : b.cartanMatrix j i = 0)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    ∃ v : P.weylGroupToPerm.range,
      rootWeylLength P b v + 2 = rootWeylLength P b w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix i j 2) = w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix j i 2) = w := by
  have hdrop : rootWeylLength P b (w * rootWeylWord P b [i, j]) + 2 =
      rootWeylLength P b w := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_two P b w i j hij hji hi hj
  obtain ⟨v, hlen, hleft, hright⟩ := commonSuffix_of_words P b w
    [i, j] [j, i] 2
    (rootWeylWord_braid_two P b i j hij hji)
    (rootWeylWord_two_mul_self P b i j hij hji) hdrop
  refine ⟨v, hlen, ?_, ?_⟩
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hright
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hleft

private theorem commonSuffix_three (w : P.weylGroupToPerm.range)
    (i j : b.support) (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    ∃ v : P.weylGroupToPerm.range,
      rootWeylLength P b v + 3 = rootWeylLength P b w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix i j 3) = w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix j i 3) = w := by
  have hdrop : rootWeylLength P b (w * rootWeylWord P b [i, j, i]) + 3 =
      rootWeylLength P b w := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_three P b w i j hij hji hi hj
  obtain ⟨v, hlen, hleft, hright⟩ := commonSuffix_of_words P b w
    [i, j, i] [j, i, j] 3
    (rootWeylWord_braid_three P b i j hij hji)
    (rootWeylWord_three_mul_self P b i j) hdrop
  refine ⟨v, hlen, ?_, ?_⟩
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hleft
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hright

private theorem commonSuffix_four (w : P.weylGroupToPerm.range)
    (i j : b.support) (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -2)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    ∃ v : P.weylGroupToPerm.range,
      rootWeylLength P b v + 4 = rootWeylLength P b w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix i j 4) = w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix j i 4) = w := by
  have hdrop : rootWeylLength P b (w * rootWeylWord P b [i, j, i, j]) + 4 =
      rootWeylLength P b w := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_four P b w i j hij hji hi hj
  obtain ⟨v, hlen, hleft, hright⟩ := commonSuffix_of_words P b w
    [i, j, i, j] [j, i, j, i] 4
    (rootWeylWord_braid_four P b i j hij hji)
    (rootWeylWord_four_mul_self P b i j hij hji) hdrop
  refine ⟨v, hlen, ?_, ?_⟩
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hright
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hleft

private theorem commonSuffix_six (w : P.weylGroupToPerm.range)
    (i j : b.support) (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -3)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    ∃ v : P.weylGroupToPerm.range,
      rootWeylLength P b v + 6 = rootWeylLength P b w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix i j 6) = w ∧
      v * wordEval (simpleWeylReflection P b) (alternatingSuffix j i 6) = w := by
  have hdrop : rootWeylLength P b (w * rootWeylWord P b [i, j, i, j, i, j]) + 6 =
      rootWeylLength P b w := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_six P b w i j hij hji hi hj
  obtain ⟨v, hlen, hleft, hright⟩ := commonSuffix_of_words P b w
    [i, j, i, j, i, j] [j, i, j, i, j, i] 6
    (rootWeylWord_braid_six P b i j hij hji)
    (rootWeylWord_six_mul_self P b i j hij hji) hdrop
  refine ⟨v, hlen, ?_, ?_⟩
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hright
  · simpa only [alternatingSuffix, List.cons_append, List.nil_append] using hleft

/-- Actual shortest length and the Cartan-defined alternating lengths satisfy
the common-suffix premise used by the generic reduced-evaluation induction. -/
theorem actualRoot_hasCommonAlternatingSuffix :
    HasCommonAlternatingSuffix (simpleWeylReflection P b) (rootWeylLength P b)
      (simpleBraidLength P b) := by
  intro w i j hij hi hj
  have hni : ¬ b.IsPos (w.val i.val) :=
    (rootWeylLength_mul_simple_lt_iff P b w i).mp (by omega)
  have hnj : ¬ b.IsPos (w.val j.val) :=
    (rootWeylLength_mul_simple_lt_iff P b w j).mp (by omega)
  rcases cartanMatrix_pair_cases_of_ne P b i j hij with
    ⟨hab, hba⟩ | ⟨hab, hba⟩ | ⟨hab, hba⟩ |
    ⟨hab, hba⟩ | ⟨hab, hba⟩ | ⟨hab, hba⟩
  · have hm : simpleBraidLength P b i j = 2 := by
      simp [simpleBraidLength, hab, hba]
    rw [hm]
    exact commonSuffix_two P b w i j hab hba hni hnj
  · have hm : simpleBraidLength P b i j = 3 := by
      simp [simpleBraidLength, hab, hba]
    rw [hm]
    exact commonSuffix_three P b w i j hab hba hni hnj
  · have hm : simpleBraidLength P b i j = 4 := by
      simp [simpleBraidLength, hab, hba]
    rw [hm]
    exact commonSuffix_four P b w i j hab hba hni hnj
  · have hm : simpleBraidLength P b i j = 4 := by
      simp [simpleBraidLength, hab, hba]
    rw [hm]
    obtain ⟨v, hlen, hleft, hright⟩ := commonSuffix_four P b w j i hba hab hnj hni
    exact ⟨v, hlen, hright, hleft⟩
  · have hm : simpleBraidLength P b i j = 6 := by
      simp [simpleBraidLength, hab, hba]
    rw [hm]
    exact commonSuffix_six P b w i j hab hba hni hnj
  · have hm : simpleBraidLength P b i j = 6 := by
      simp [simpleBraidLength, hab, hba]
    rw [hm]
    obtain ⟨v, hlen, hleft, hright⟩ := commonSuffix_six P b w j i hba hab hnj hni
    exact ⟨v, hlen, hright, hleft⟩

end Atlas.Chevalley.RootData
