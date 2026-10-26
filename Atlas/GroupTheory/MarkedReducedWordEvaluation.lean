import Atlas.GroupTheory.ReducedWordEvaluation
import Mathlib.Algebra.Group.End
import Mathlib.Data.Set.Function

/-! Marked reduced words via endomorphisms of sets.
The target lifts need not be involutions. Ordinary braid products and the
corresponding finite marked-set identities are separate explicit hypotheses.
No actual root-family coherence or inversion-label uniqueness is assumed. -/

namespace Atlas.GroupTheory.ReducedWords

variable {I G Mark : Type*} [Monoid G]

/-- Prefix-transported marks, retaining their full data rather than just labels. -/
def markedWordSet (t : I → G) (act : G →* Function.End Mark) (mark : I → Mark) :
    List I → Set Mark
  | [] => ∅
  | i :: l => {mark i} ∪ act (t i) '' markedWordSet t act mark l

/-- A letter acts on sets by adjoining its mark and transporting the old set. -/
def markedLetterEnd (t : I → G) (act : G →* Function.End Mark) (mark : I → Mark)
    (i : I) : Function.End (Set Mark) :=
  fun S => {mark i} ∪ act (t i) '' S

@[simp] theorem markedWordSet_nil (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) : markedWordSet t act mark [] = ∅ := rfl

@[simp] theorem markedWordSet_cons (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (i : I) (l : List I) :
    markedWordSet t act mark (i :: l) =
      {mark i} ∪ act (t i) '' markedWordSet t act mark l := rfl

/-- The accumulated set consists of the prefix marks and the transported input.
This is the bridge to the already proved monoid-target reduced-word theorem. -/
theorem markedLetterEnd_wordEval_apply (t : I → G)
    (act : G →* Function.End Mark) (mark : I → Mark) (l : List I) (S : Set Mark) :
    wordEval (markedLetterEnd t act mark) l S =
      markedWordSet t act mark l ∪ act (wordEval t l) '' S := by
  induction l with
  | nil =>
    simp only [wordEval_nil, markedWordSet_nil, map_one]
    change S = ∅ ∪ id '' S
    simp
  | cons i l ih =>
    change markedLetterEnd t act mark i
        (wordEval (markedLetterEnd t act mark) l S) =
      markedWordSet t act mark (i :: l) ∪ act (t i * wordEval t l) '' S
    rw [ih, map_mul]
    change {mark i} ∪ act (t i) ''
        (markedWordSet t act mark l ∪ act (wordEval t l) '' S) =
      ({mark i} ∪ act (t i) '' markedWordSet t act mark l) ∪
        (act (t i) ∘ act (wordEval t l)) '' S
    erw [Set.image_union, Set.image_image, Set.union_assoc]
    rfl

@[simp] theorem markedLetterEnd_wordEval_empty (t : I → G)
    (act : G →* Function.End Mark) (mark : I → Mark) (l : List I) :
    wordEval (markedLetterEnd t act mark) l ∅ = markedWordSet t act mark l := by
  erw [markedLetterEnd_wordEval_apply, Set.image_empty, Set.union_empty]

/-- Appending words transports the second set by the full first lift. -/
theorem markedWordSet_append (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (l r : List I) :
    markedWordSet t act mark (l ++ r) =
      markedWordSet t act mark l ∪ act (wordEval t l) '' markedWordSet t act mark r := by
  rw [← markedLetterEnd_wordEval_empty t act mark (l ++ r), wordEval_append]
  change wordEval (markedLetterEnd t act mark) l
      (wordEval (markedLetterEnd t act mark) r ∅) = _
  rw [markedLetterEnd_wordEval_empty, markedLetterEnd_wordEval_apply]

/-- The mark at any specified position is retained with its actual prefix lift. -/
theorem prefix_mark_mem_markedWordSet (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (p r : List I) (i : I) :
    act (wordEval t p) (mark i) ∈ markedWordSet t act mark (p ++ i :: r) := by
  rw [markedWordSet_append]
  apply Set.mem_union_right
  apply Set.mem_image_of_mem
  exact Set.mem_union_left _ (Set.mem_singleton (mark i))

/-- Both the actual product and the marked set are needed for equality of the
set endomorphisms. A braid identity for the products alone is insufficient. -/
theorem markedLetterEnd_wordEval_eq_of_product_and_marks (t : I → G)
    (act : G →* Function.End Mark) (mark : I → Mark) {l r : List I}
    (hproduct : wordEval t l = wordEval t r)
    (hmarks : markedWordSet t act mark l = markedWordSet t act mark r) :
    wordEval (markedLetterEnd t act mark) l =
      wordEval (markedLetterEnd t act mark) r := by
  funext S
  rw [markedLetterEnd_wordEval_apply, markedLetterEnd_wordEval_apply, hproduct, hmarks]

section Reduced

variable {W : Type*} [Group W] {s : I → W} {length : W → ℕ}

/-- Local product braids and local marked braids imply independence of the
entire set endomorphism for reduced expressions of the same source element.
All length, representative and common-suffix data remain explicit. -/
theorem reduced_markedLetterEnd_wordEval_eq_of_alternating
    (D : LengthData s length) (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (m : I → I → ℕ)
    (hpositive : ∀ i j, i ≠ j → 0 < m i j)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCommonAlternatingSuffix s length m)
    (hbraid : ∀ i j, i ≠ j →
      wordEval t (alternatingSuffix i j (m i j)) =
        wordEval t (alternatingSuffix j i (m i j)))
    (hmarks : ∀ i j, i ≠ j →
      markedWordSet t act mark (alternatingSuffix i j (m i j)) =
        markedWordSet t act mark (alternatingSuffix j i (m i j)))
    {l r : List I} (hl : IsReduced s length l) (hr : IsReduced s length r)
    (heq : wordEval s l = wordEval s r) :
    wordEval (markedLetterEnd t act mark) l =
      wordEval (markedLetterEnd t act mark) r := by
  apply reduced_wordEval_eq_of_alternating D (markedLetterEnd t act mark) m
    hpositive hrep hsuffix ?_ hl hr heq
  intro i j hij
  exact markedLetterEnd_wordEval_eq_of_product_and_marks t act mark
    (hbraid i j hij) (hmarks i j hij)

/-- The prefix-transported marked set is independent of reduced expression
once the explicit local marked braid obligations have been discharged. -/
theorem reduced_markedWordSet_eq_of_alternating
    (D : LengthData s length) (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (m : I → I → ℕ)
    (hpositive : ∀ i j, i ≠ j → 0 < m i j)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCommonAlternatingSuffix s length m)
    (hbraid : ∀ i j, i ≠ j →
      wordEval t (alternatingSuffix i j (m i j)) =
        wordEval t (alternatingSuffix j i (m i j)))
    (hmarks : ∀ i j, i ≠ j →
      markedWordSet t act mark (alternatingSuffix i j (m i j)) =
        markedWordSet t act mark (alternatingSuffix j i (m i j)))
    {l r : List I} (hl : IsReduced s length l) (hr : IsReduced s length r)
    (heq : wordEval s l = wordEval s r) :
    markedWordSet t act mark l = markedWordSet t act mark r := by
  have h := reduced_markedLetterEnd_wordEval_eq_of_alternating D t act mark m
    hpositive hrep hsuffix hbraid hmarks hl hr heq
  have hv := congrArg (fun f : Function.End (Set Mark) => f ∅) h
  simpa only [markedLetterEnd_wordEval_empty] using hv

end Reduced
end Atlas.GroupTheory.ReducedWords
