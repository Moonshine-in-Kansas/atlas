import Atlas.GroupTheory.LabelledSubgroupMarks

/-! Six-letter marked-set comparison from the two actual middle fixedness
obligations and explicitly stated square normalizations. -/
namespace Atlas.GroupTheory.ReducedWords
variable {I G Mark : Type*} [Monoid G]

theorem markedWordSet_six_of_middle_fixed (t : I → G)
    (act : G →* Function.End Mark) (mark : I → Mark) (i j : I)
    (hshort : act (t j) (act (t i) (act (t j) (mark i))) =
      act (t i) (act (t j) (mark i)))
    (hlong : act (t i) (act (t j) (act (t i) (mark j))) =
      act (t j) (act (t i) (mark j)))
    (hisq : act (t i) (act (t i) (mark j)) = mark j)
    (hjsq : act (t j) (act (t j) (mark i)) = mark i)
    (hisqj : act (t i) (act (t i) (act (t j) (mark i))) =
      act (t j) (mark i))
    (hjsqi : act (t j) (act (t j) (act (t i) (mark j))) =
      act (t i) (mark j)) :
    markedWordSet t act mark [i,j,i,j,i,j] =
      markedWordSet t act mark [j,i,j,i,j,i] := by
  simp only [markedWordSet]
  repeat' first
    | erw [Set.image_union]
    | erw [Set.image_empty]
    | erw [Set.image_singleton]
    | rw [Set.union_empty]
  simp only [hshort, hlong, hisqj, hjsqi, hisq, hjsq]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff]
  tauto

end Atlas.GroupTheory.ReducedWords
