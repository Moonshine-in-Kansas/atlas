import Atlas.GroupTheory.MarkedReducedWordEvaluation
import Mathlib.Data.List.Nodup

/-! Ordered marks make label uniqueness independent of any group construction. -/
namespace Atlas.GroupTheory.ReducedWords
variable {I G Mark Label Value : Type*} [Monoid G]

/-- The ordered version of the existing prefix-transported marked set. -/
def markedWordList (t : I → G) (act : G →* Function.End Mark) (mark : I → Mark) :
    List I → List Mark
  | [] => []
  | i :: l => mark i :: (markedWordList t act mark l).map (act (t i))

theorem mem_markedWordList_iff (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (l : List I) (x : Mark) :
    x ∈ markedWordList t act mark l ↔ x ∈ markedWordSet t act mark l := by
  induction l generalizing x with
  | nil => simp only [markedWordList, markedWordSet, List.not_mem_nil, Set.mem_empty_iff_false]
  | cons i l ih =>
    simp only [markedWordList, markedWordSet, List.mem_cons,
      Set.mem_union, Set.mem_singleton_iff]
    erw [List.mem_map, Set.mem_image]
    simp only [ih]

/-- Distinct occurrences cannot carry the same label when the label list has
no repetitions. The marks themselves can have arbitrary additional data. -/
theorem eq_of_mem_of_nodup_labels (label : Mark → Label) (l : List Mark)
    (hlabels : (l.map label).Nodup) {x y : Mark}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : label x = label y) : x = y := by
  exact List.inj_on_of_nodup_map hlabels hx hy hxy

/-- A label occurring in a paired list with distinct labels has one value. -/
theorem existsUnique_value_of_mem_nodup_labels (l : List (Label × Value))
    (hlabels : (l.map Prod.fst).Nodup) {β : Label}
    (hβ : β ∈ l.map Prod.fst) : ∃! v : Value, (β, v) ∈ l := by
  obtain ⟨⟨γ, v⟩, hv, hγ⟩ := List.mem_map.mp hβ
  change γ = β at hγ
  subst γ
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact congrArg Prod.snd (eq_of_mem_of_nodup_labels Prod.fst l hlabels hw hv rfl)

end Atlas.GroupTheory.ReducedWords
