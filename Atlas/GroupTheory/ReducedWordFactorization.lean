import Atlas.GroupTheory.ReducedWordEvaluation
import Mathlib.Data.List.Induction
import Mathlib.Algebra.Group.Hom.Defs

/-! Conditional factorization of word evaluation through an actual group.
The explicit concrete suffix and length premises are not discharged here. -/

noncomputable section
namespace Atlas.GroupTheory.ReducedWords

variable {I W H : Type*} [Group W] [Monoid H]
  {s : I → W} {length : W → ℕ}

def reducedChoice
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (w : W) : List I := Classical.choose (hrep w)

theorem reducedChoice_eval
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (w : W) : wordEval s (reducedChoice hrep w) = w :=
  (Classical.choose_spec (hrep w)).1

theorem reducedChoice_length
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (w : W) : (reducedChoice hrep w).length = length w :=
  (Classical.choose_spec (hrep w)).2

theorem reducedChoice_isReduced
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (w : W) : IsReduced s length (reducedChoice hrep w) := by
  rw [IsReduced, reducedChoice_eval, reducedChoice_length]

def reducedLift (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (w : W) : H := wordEval t (reducedChoice hrep w)

variable (D : LengthData s length)

include D in
theorem reducedLift_eq_wordEval (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    {w : W} {l : List I} (hl : IsReduced s length l) (hw : wordEval s l = w) :
    reducedLift t hrep w = wordEval t l :=
  reduced_wordEval_eq D t hsuffix (reducedChoice_isReduced hrep w) hl
    ((reducedChoice_eval hrep w).trans hw.symm)

include D in
theorem reducedLift_one (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t) :
    reducedLift t hrep 1 = 1 := by
  have hzero : length (1 : W) = 0 := by
    have h := D.word_bound ([] : List I)
    simpa only [wordEval_nil, List.length_nil, Nat.le_zero] using h
  have hnil : IsReduced s length [] := by
    simpa only [IsReduced, wordEval_nil, List.length_nil] using hzero
  exact (reducedLift_eq_wordEval D t hrep hsuffix hnil (wordEval_nil s)).trans
    (wordEval_nil t)

include D in
theorem reducedLift_mul_simple_of_ascent (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    (w : W) (i : I) (hup : length (w * s i) = length w + 1) :
    reducedLift t hrep (w * s i) = reducedLift t hrep w * t i := by
  have hword : wordEval s (reducedChoice hrep w ++ [i]) = w * s i := by
    rw [wordEval_append_singleton, reducedChoice_eval]
  have hred : IsReduced s length (reducedChoice hrep w ++ [i]) := by
    dsimp only [IsReduced]
    rw [hword, List.length_append, List.length_singleton, reducedChoice_length]
    exact hup
  rw [reducedLift_eq_wordEval D t hrep hsuffix hred hword, wordEval_append_singleton]
  rfl

include D in
/-- Generator involutions are needed here, when a nonreduced word makes a
length-decreasing step. No additional target relation is assumed. -/
theorem reducedLift_mul_simple (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    (hsquare : ∀ i, t i * t i = 1)
    (hstep : ∀ w i, length (w * s i) + 1 = length w ∨
      length (w * s i) = length w + 1)
    (w : W) (i : I) :
    reducedLift t hrep (w * s i) = reducedLift t hrep w * t i := by
  rcases hstep w i with hdown | hup
  · have hcancel : w * s i * s i = w := by rw [mul_assoc, D.square, mul_one]
    have hup : length ((w * s i) * s i) = length (w * s i) + 1 := by
      rw [hcancel]
      exact hdown.symm
    have h := reducedLift_mul_simple_of_ascent D t hrep hsuffix (w * s i) i hup
    rw [hcancel] at h
    calc
      reducedLift t hrep (w * s i) =
          (reducedLift t hrep (w * s i) * t i) * t i := by
        rw [mul_assoc, hsquare, mul_one]
      _ = reducedLift t hrep w * t i := congrArg (fun x => x * t i) h.symm
  · exact reducedLift_mul_simple_of_ascent D t hrep hsuffix w i hup

include D in
theorem reducedLift_wordEval (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    (hsquare : ∀ i, t i * t i = 1)
    (hstep : ∀ w i, length (w * s i) + 1 = length w ∨
      length (w * s i) = length w + 1) (l : List I) :
    reducedLift t hrep (wordEval s l) = wordEval t l := by
  induction l using List.reverseRecOn with
  | nil => simpa only [wordEval_nil] using reducedLift_one D t hrep hsuffix
  | append_singleton l i ih =>
    rw [wordEval_append_singleton,
      reducedLift_mul_simple D t hrep hsuffix hsquare hstep, ih,
      wordEval_append_singleton]

include D in
/-- Actual evaluation into any target with the displayed braid and involution
relations factors through W, conditional on the concrete source length and
common-suffix facts. This is not a claim that any ATLAS normalizer has supplied
those facts yet. -/
def evaluationHom (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    (hsquare : ∀ i, t i * t i = 1)
    (hstep : ∀ w i, length (w * s i) + 1 = length w ∨
      length (w * s i) = length w + 1) : W →* H where
  toFun := reducedLift t hrep
  map_one' := reducedLift_one D t hrep hsuffix
  map_mul' w v := by
    obtain ⟨l, hl, _⟩ := hrep w
    obtain ⟨r, hr, _⟩ := hrep v
    have hword : wordEval s (l ++ r) = w * v := by rw [wordEval_append, hl, hr]
    calc
      reducedLift t hrep (w * v) = reducedLift t hrep (wordEval s (l ++ r)) :=
        congrArg (reducedLift t hrep) hword.symm
      _ = wordEval t (l ++ r) := reducedLift_wordEval D t hrep hsuffix hsquare hstep _
      _ = wordEval t l * wordEval t r := wordEval_append t l r
      _ = reducedLift t hrep w * reducedLift t hrep v := by
        rw [← reducedLift_wordEval D t hrep hsuffix hsquare hstep l,
          ← reducedLift_wordEval D t hrep hsuffix hsquare hstep r, hl, hr]

theorem evaluationHom_wordEval (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    (hsquare : ∀ i, t i * t i = 1)
    (hstep : ∀ w i, length (w * s i) + 1 = length w ∨
      length (w * s i) = length w + 1) (l : List I) :
    evaluationHom D t hrep hsuffix hsquare hstep (wordEval s l) = wordEval t l :=
  reducedLift_wordEval D t hrep hsuffix hsquare hstep l

theorem evaluationHom_simple (t : I → H)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    (hsquare : ∀ i, t i * t i = 1)
    (hstep : ∀ w i, length (w * s i) + 1 = length w ∨
      length (w * s i) = length w + 1) (i : I) :
    evaluationHom D t hrep hsuffix hsquare hstep (s i) = t i := by
  simpa only [wordEval_singleton] using
    evaluationHom_wordEval D t hrep hsuffix hsquare hstep [i]

end Atlas.GroupTheory.ReducedWords
