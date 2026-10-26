import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Init
import Lean.Elab.Tactic.Omega

/-! Evaluation of reduced words from concrete length and common-suffix data.
All hypotheses are explicit. No abstract Coxeter presentation is imported. -/

noncomputable section
namespace Atlas.GroupTheory.ReducedWords

variable {I W H : Type*} [Group W] [Monoid H]

def wordEval {G : Type*} [Monoid G] (s : I → G) (l : List I) : G :=
  (l.map s).prod

@[simp] theorem wordEval_nil {G : Type*} [Monoid G] (s : I → G) :
    wordEval s [] = 1 := rfl

@[simp] theorem wordEval_singleton {G : Type*} [Monoid G] (s : I → G) (i : I) :
    wordEval s [i] = s i := by simp [wordEval]

theorem wordEval_append {G : Type*} [Monoid G] (s : I → G) (l r : List I) :
    wordEval s (l ++ r) = wordEval s l * wordEval s r := by
  simp only [wordEval, List.map_append, List.prod_append]

@[simp] theorem wordEval_append_singleton {G : Type*} [Monoid G]
    (s : I → G) (l : List I) (i : I) :
    wordEval s (l ++ [i]) = wordEval s l * s i := by
  rw [wordEval_append, wordEval_singleton]

def IsReduced (s : I → W) (length : W → ℕ) (l : List I) : Prop :=
  length (wordEval s l) = l.length

/-- Elementary properties of an actual shortest-word length. These do not
assert any presentation or any reduced-word independence. -/
structure LengthData (s : I → W) (length : W → ℕ) : Prop where
  square : ∀ i, s i * s i = 1
  word_bound : ∀ l, length (wordEval s l) ≤ l.length
  step_bound : ∀ w i, length (w * s i) ≤ length w + 1

variable {s : I → W} {length : W → ℕ} (D : LengthData s length)

include D in
theorem reduced_append_singleton_prefix {l : List I} {i : I}
    (h : IsReduced s length (l ++ [i])) : IsReduced s length l := by
  have hbound := D.word_bound l
  have hstep := D.step_bound (wordEval s l) i
  dsimp only [IsReduced] at h ⊢
  rw [wordEval_append_singleton, List.length_append, List.length_singleton] at h
  omega

include D in
theorem reduced_append_singleton_lt {l : List I} {i : I}
    (h : IsReduced s length (l ++ [i])) :
    length (wordEval s l) < length (wordEval s (l ++ [i])) := by
  have hp := reduced_append_singleton_prefix D h
  dsimp only [IsReduced] at h hp
  rw [List.length_append, List.length_singleton] at h
  omega

include D in
theorem reduced_append_singleton_descent {l : List I} {i : I}
    (h : IsReduced s length (l ++ [i])) :
    length (wordEval s (l ++ [i]) * s i) + 1 =
      length (wordEval s (l ++ [i])) := by
  have hp := reduced_append_singleton_prefix D h
  dsimp only [IsReduced] at h hp
  have hcancel : wordEval s (l ++ [i]) * s i = wordEval s l := by
    rw [wordEval_append_singleton, mul_assoc, D.square, mul_one]
  rw [hcancel, hp, h, List.length_append, List.length_singleton]

/-- Explicit local premise used in the induction. At two distinct right
descents, two reduced representatives have one common prefix, end in the two
specified letters, and their remaining suffixes have equal target evaluation.
An alternating-braid adapter below constructs this from usual suffix data. -/
def HasCompatibleDescentSuffix (s : I → W) (length : W → ℕ) (t : I → H) : Prop :=
  ∀ (w : W) (i j : I), i ≠ j →
    length (w * s i) + 1 = length w →
    length (w * s j) + 1 = length w →
    ∃ p a b : List I,
      IsReduced s length ((p ++ a) ++ [i]) ∧
      IsReduced s length ((p ++ b) ++ [j]) ∧
      wordEval s ((p ++ a) ++ [i]) = w ∧
      wordEval s ((p ++ b) ++ [j]) = w ∧
      wordEval t (a ++ [i]) = wordEval t (b ++ [j])

include D in
/-- Matsumoto induction in the form needed for well-defined reduced
evaluation. The only target equalities assumed are the explicit local suffix
identities. Even target-generator involutions are unnecessary at this stage. -/
theorem reduced_wordEval_eq (t : I → H)
    (hsuffix : HasCompatibleDescentSuffix s length t)
    {l r : List I} (hl : IsReduced s length l) (hr : IsReduced s length r)
    (heq : wordEval s l = wordEval s r) : wordEval t l = wordEval t r := by
  classical
  have main : ∀ n : ℕ, ∀ w : W, length w = n →
      ∀ l r : List I, IsReduced s length l → IsReduced s length r →
        wordEval s l = w → wordEval s r = w → wordEval t l = wordEval t r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn l r hl hr hwl hwr
      have hlen : l.length = r.length := by
        have hll := hl
        have hrr := hr
        dsimp only [IsReduced] at hll hrr
        rw [hwl] at hll
        rw [hwr] at hrr
        omega
      rcases List.eq_nil_or_concat' l with rfl | ⟨a, i, rfl⟩
      · have hrnil : r = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
        subst r
        rfl
      · rcases List.eq_nil_or_concat' r with rfl | ⟨b, j, rfl⟩
        · simp only [List.length_append, List.length_singleton, List.length_nil] at hlen
          omega
        · have ha := reduced_append_singleton_prefix D hl
          have hb := reduced_append_singleton_prefix D hr
          have hltA : length (wordEval s a) < n := by
            have hh := reduced_append_singleton_lt D hl
            rwa [hwl, hn] at hh
          have hltB : length (wordEval s b) < n := by
            have hh := reduced_append_singleton_lt D hr
            rwa [hwr, hn] at hh
          by_cases hij : i = j
          · subst j
            have hab : wordEval s a = wordEval s b := by
              apply mul_right_cancel (b := s i)
              simpa only [wordEval_append_singleton] using hwl.trans hwr.symm
            have hval := ih (length (wordEval s a)) hltA (wordEval s a) rfl
              a b ha hb rfl hab.symm
            simpa only [wordEval_append_singleton] using congrArg (fun x => x * t i) hval
          · have hdi : length (w * s i) + 1 = length w := by
              simpa only [hwl] using reduced_append_singleton_descent D hl
            have hdj : length (w * s j) + 1 = length w := by
              simpa only [hwr] using reduced_append_singleton_descent D hr
            obtain ⟨p, u, v, hpu, hpv, hpuw, hpvw, hbraid⟩ :=
              hsuffix w i j hij hdi hdj
            have hpup := reduced_append_singleton_prefix D hpu
            have hpvp := reduced_append_singleton_prefix D hpv
            have hau : wordEval s a = wordEval s (p ++ u) := by
              apply mul_right_cancel (b := s i)
              simpa only [wordEval_append_singleton] using hwl.trans hpuw.symm
            have hbv : wordEval s b = wordEval s (p ++ v) := by
              apply mul_right_cancel (b := s j)
              simpa only [wordEval_append_singleton] using hwr.trans hpvw.symm
            have hevA := ih (length (wordEval s a)) hltA (wordEval s a) rfl
              a (p ++ u) ha hpup rfl hau.symm
            have hevB := ih (length (wordEval s b)) hltB (wordEval s b) rfl
              b (p ++ v) hb hpvp rfl hbv.symm
            calc
              wordEval t (a ++ [i]) = wordEval t a * t i := wordEval_append_singleton _ _ _
              _ = wordEval t (p ++ u) * t i := congrArg (fun x => x * t i) hevA
              _ = wordEval t p * wordEval t (u ++ [i]) := by
                simp only [wordEval_append, wordEval_singleton, mul_assoc]
              _ = wordEval t p * wordEval t (v ++ [j]) := congrArg (fun x => wordEval t p * x) hbraid
              _ = wordEval t (p ++ v) * t j := by
                simp only [wordEval_append, wordEval_singleton, mul_assoc]
              _ = wordEval t b * t j := congrArg (fun x => x * t j) hevB.symm
              _ = wordEval t (b ++ [j]) := (wordEval_append_singleton _ _ _).symm
  exact main (length (wordEval s l)) (wordEval s l) rfl l r hl hr rfl heq.symm

/-- An alternating word whose last letter is the first displayed generator.
This elementary list definition does not depend on Coxeter machinery. -/
def alternatingSuffix (i j : I) : ℕ → List I
  | 0 => []
  | n + 1 => alternatingSuffix j i n ++ [i]

@[simp] theorem alternatingSuffix_succ (i j : I) (n : ℕ) :
    alternatingSuffix i j (n + 1) = alternatingSuffix j i n ++ [i] := rfl

@[simp] theorem length_alternatingSuffix (i j : I) (n : ℕ) :
    (alternatingSuffix i j n).length = n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [alternatingSuffix_succ, List.length_append,
      List.length_singleton, ih]

/-- The actual common alternating suffix obligation, stated separately from
target braid identities and without a Coxeter-system premise. -/
def HasCommonAlternatingSuffix (s : I → W) (length : W → ℕ)
    (m : I → I → ℕ) : Prop :=
  ∀ (w : W) (i j : I), i ≠ j →
    length (w * s i) + 1 = length w →
    length (w * s j) + 1 = length w →
    ∃ v : W, length v + m i j = length w ∧
      v * wordEval s (alternatingSuffix i j (m i j)) = w ∧
      v * wordEval s (alternatingSuffix j i (m i j)) = w

theorem compatibleDescentSuffix_of_alternating (t : I → H) (m : I → I → ℕ)
    (hpositive : ∀ i j, i ≠ j → 0 < m i j)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCommonAlternatingSuffix s length m)
    (hbraid : ∀ i j, i ≠ j →
      wordEval t (alternatingSuffix i j (m i j)) =
        wordEval t (alternatingSuffix j i (m i j))) :
    HasCompatibleDescentSuffix s length t := by
  intro w i j hij hi hj
  obtain ⟨v, hlen, hvi, hvj⟩ := hsuffix w i j hij hi hj
  obtain ⟨p, hp, hplen⟩ := hrep v
  cases hm : m i j with
  | zero =>
    have h := hpositive i j hij
    omega
  | succ n =>
    have hpi : wordEval s ((p ++ alternatingSuffix j i n) ++ [i]) = w := by
      simpa only [hm, alternatingSuffix_succ, wordEval_append,
        wordEval_singleton, hp, mul_assoc] using hvi
    have hpj : wordEval s ((p ++ alternatingSuffix i j n) ++ [j]) = w := by
      simpa only [hm, alternatingSuffix_succ, wordEval_append,
        wordEval_singleton, hp, mul_assoc] using hvj
    refine ⟨p, alternatingSuffix j i n, alternatingSuffix i j n, ?_, ?_, hpi, hpj, ?_⟩
    · dsimp only [IsReduced]
      rw [hpi, List.length_append, List.length_append, List.length_singleton,
        length_alternatingSuffix, hplen]
      omega
    · dsimp only [IsReduced]
      rw [hpj, List.length_append, List.length_append, List.length_singleton,
        length_alternatingSuffix, hplen]
      omega
    · simpa only [hm, alternatingSuffix_succ] using hbraid i j hij

include D in
theorem reduced_wordEval_eq_of_alternating (t : I → H) (m : I → I → ℕ)
    (hpositive : ∀ i j, i ≠ j → 0 < m i j)
    (hrep : ∀ w : W, ∃ p : List I, wordEval s p = w ∧ p.length = length w)
    (hsuffix : HasCommonAlternatingSuffix s length m)
    (hbraid : ∀ i j, i ≠ j →
      wordEval t (alternatingSuffix i j (m i j)) =
        wordEval t (alternatingSuffix j i (m i j)))
    {l r : List I} (hl : IsReduced s length l) (hr : IsReduced s length r)
    (heq : wordEval s l = wordEval s r) : wordEval t l = wordEval t r :=
  reduced_wordEval_eq D t
    (compatibleDescentSuffix_of_alternating t m hpositive hrep hsuffix hbraid) hl hr heq

end Atlas.GroupTheory.ReducedWords
