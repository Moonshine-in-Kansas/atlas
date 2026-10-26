import Atlas.GroupTheory.ReducedWordEvaluation
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! Actual root-permutation length inputs to the generic reduced-evaluation
argument. This does not supply the common alternating suffix interface. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
open Atlas.GroupTheory.ReducedWords

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The generic length hypotheses hold for the actual root-permutation Weyl
image and its previously constructed shortest simple-reflection length. -/
def actualRootLengthData :
    LengthData (simpleWeylReflection P b) (rootWeylLength P b) where
  square := simpleWeylReflection_mul_self P b
  word_bound := rootWeylWord_length_le P b
  step_bound := rootWeylLength_mul_simple_le P b

theorem root_wordEval_eq_rootWeylWord (l : List b.support) :
    wordEval (simpleWeylReflection P b) l = rootWeylWord P b l := rfl

theorem root_reduced_representatives (w : P.weylGroupToPerm.range) :
    ∃ l : List b.support, wordEval (simpleWeylReflection P b) l = w ∧
      l.length = rootWeylLength P b w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
  refine ⟨l, ?_, hlen⟩
  apply Subtype.ext
  change (rootWeylWord P b l).val = w.val
  rw [rootWeylWord_val]
  exact hl

theorem root_length_step_cases (w : P.weylGroupToPerm.range) (i : b.support) :
    rootWeylLength P b (w * simpleWeylReflection P b i) + 1 = rootWeylLength P b w ∨
      rootWeylLength P b (w * simpleWeylReflection P b i) = rootWeylLength P b w + 1 := by
  by_cases hpos : b.IsPos (w.val i.val)
  · exact Or.inr (rootWeylLength_mul_simple_of_positive P b w i hpos)
  · exact Or.inl (rootWeylLength_mul_simple_of_negative P b w i hpos)

end Atlas.Chevalley.RootData
