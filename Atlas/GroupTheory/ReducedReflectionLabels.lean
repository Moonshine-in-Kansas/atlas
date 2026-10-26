import Atlas.GroupTheory.ReducedWordEvaluation
import Mathlib.Tactic.Group

/-! Distinct prefix-conjugate reflections in a reduced involution word.
Equal reflection marks delete two letters, contradicting the length bound.
No presentation, braid theorem, root system or representation is required. -/

namespace Atlas.GroupTheory.ReducedWords
variable {I W : Type*} [Group W] (s : I → W)

/-- Equality of two prefix-conjugate reflections removes exactly their two
letters from the represented element. Only the simple squares are used. -/
theorem wordEval_delete_two_of_prefix_reflections_eq
    (hsquare : ∀ i, s i * s i = 1) (p r z : List I) (i j : I)
    (hreflection :
      wordEval s p * s i * (wordEval s p)⁻¹ =
        wordEval s (p ++ i :: r) * s j * (wordEval s (p ++ i :: r))⁻¹) :
    wordEval s (p ++ i :: (r ++ j :: z)) = wordEval s ((p ++ r) ++ z) := by
  let a := wordEval s p
  let c := wordEval s r
  let e := wordEval s z
  have hp : wordEval s (p ++ i :: r) = a * s i * c := by
    dsimp only [a, c]
    simp only [wordEval, List.map_append, List.prod_append, List.map_cons,
      List.prod_cons, mul_assoc]
  rw [hp] at hreflection
  change a * s i * a⁻¹ = (a * s i * c) * s j * (a * s i * c)⁻¹ at hreflection
  have hm : s i * (s i * c) = (s i * c) * s j := by
    calc
      s i * (s i * c) = a⁻¹ * (a * s i * a⁻¹) * (a * s i * c) := by group
      _ = a⁻¹ * ((a * s i * c) * s j * (a * s i * c)⁻¹) *
          (a * s i * c) := by rw [hreflection]
      _ = (s i * c) * s j := by group
  have hc : (s i * c) * s j = c := by
    rw [← mul_assoc, hsquare i, one_mul] at hm
    exact hm.symm
  simp only [wordEval, List.map_append, List.prod_append, List.map_cons, List.prod_cons]
  change a * (s i * (c * (s j * e))) = (a * c) * e
  calc
    a * (s i * (c * (s j * e))) = a * (((s i * c) * s j) * e) := by group
    _ = a * (c * e) := by rw [hc]
    _ = (a * c) * e := (mul_assoc _ _ _).symm

/-- Two different positions of a reduced word have different reflection marks.
This is a minimum-length obstruction, not a Coxeter-system theorem. -/
theorem reduced_prefix_reflections_ne {length : W → ℕ}
    (D : LengthData s length) (p r z : List I) (i j : I)
    (hred : IsReduced s length (p ++ i :: (r ++ j :: z))) :
    wordEval s p * s i * (wordEval s p)⁻¹ ≠
      wordEval s (p ++ i :: r) * s j * (wordEval s (p ++ i :: r))⁻¹ := by
  intro heq
  have hdelete := wordEval_delete_two_of_prefix_reflections_eq s D.square p r z i j heq
  have hbound := D.word_bound ((p ++ r) ++ z)
  change length (wordEval s (p ++ i :: (r ++ j :: z))) =
    (p ++ i :: (r ++ j :: z)).length at hred
  rw [hdelete] at hred
  simp only [List.length_append, List.length_cons] at hred hbound
  omega

end Atlas.GroupTheory.ReducedWords
