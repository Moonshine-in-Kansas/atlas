import Atlas.GroupTheory.ReducedReflectionLabels
import Atlas.LinearGroups.Chevalley.RootData.ReducedEvaluationData

/-! Actual root labels at different positions of a reduced root word are
distinct and positive. No root-subgroup coherence or group order is used. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical Atlas.GroupTheory.ReducedWords

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Equal labels would give equal conjugate reflections and hence a two-letter
deletion. This holds for any two displayed positions of an actual reduced word. -/
theorem isReducedRootWord_prefix_labels_ne (p r z : List b.support) (i j : b.support)
    (hred : IsReducedRootWord P b (p ++ i :: (r ++ j :: z))) :
    (rootWeylWord P b p).val i.val ≠
      (rootWeylWord P b (p ++ i :: r)).val j.val := by
  intro heq
  have hgeneric : IsReduced (simpleWeylReflection P b) (rootWeylLength P b)
      (p ++ i :: (r ++ j :: z)) := hred
  apply reduced_prefix_reflections_ne (simpleWeylReflection P b)
    (actualRootLengthData P b) p r z i j hgeneric
  apply Subtype.ext
  change (rootWeylWord P b p).val * P.reflectionPerm i.val *
      (rootWeylWord P b p).val⁻¹ =
    (rootWeylWord P b (p ++ i :: r)).val * P.reflectionPerm j.val *
      (rootWeylWord P b (p ++ i :: r)).val⁻¹
  have href := congrArg P.reflectionPerm heq
  simpa only [rootWeylWord_val, simpleReflectionWord_conjugate] using href

/-- Every displayed prefix-root mark of a reduced word is positive. -/
theorem isReducedRootWord_prefix_label_pos (p r : List b.support) (i : b.support)
    (hred : IsReducedRootWord P b (p ++ i :: r)) :
    b.IsPos ((rootWeylWord P b p).val i.val) := by
  have hsplit : IsReducedRootWord P b ((p ++ [i]) ++ r) := by
    simpa only [List.append_assoc, List.singleton_append] using hred
  have hp := (isReducedRootWord_append_parts P b (p ++ [i]) r hsplit).1
  have hprev := (isReducedRootWord_append_parts P b p [i] hp).1
  by_contra hneg
  have hstep := rootWeylLength_mul_simple_of_negative P b (rootWeylWord P b p) i hneg
  have hword : rootWeylWord P b (p ++ [i]) =
      rootWeylWord P b p * simpleWeylReflection P b i := by
    rw [rootWeylWord_append]
    simp only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
  change rootWeylLength P b (rootWeylWord P b (p ++ [i])) = (p ++ [i]).length at hp
  change rootWeylLength P b (rootWeylWord P b p) = p.length at hprev
  rw [hword, List.length_append, List.length_singleton] at hp
  omega

end Atlas.Chevalley.RootData
