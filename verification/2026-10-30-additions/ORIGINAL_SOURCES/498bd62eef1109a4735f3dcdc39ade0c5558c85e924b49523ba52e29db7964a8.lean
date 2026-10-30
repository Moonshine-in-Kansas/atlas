import FamilyWork.InvariantSimpleDescent
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-!
Staged continuation, 27 October 2026. Exact verification receipts are separate.

The four actual folded Weyl permutations, exact bounded descent, and generation
of every diagram-fixed permutation by a word whose total weight is its inherited
E6 length. The same word supplies an actual fixed companion-normalizer lift.
There is no F4 identification, Weyl enumeration, weighted-sum evaluation, or
Bruhat premise or conclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.TwistedE6

open Classical RootData Atlas.Comparisons.E6Lattice

local instance foldedGenerationRootFintype : Fintype E6Data.Root := Fintype.ofFinite _

/-- Public Chevalley labels: the two exchanged pairs, then the two fixed nodes.
This is the same order as `foldedWeylInN`, whose internal labels are lattice labels. -/
def e6FoldedWeylGenerator (a : Fin 4) : E6RootWeyl :=
  match a with
  | 0 => e6RootSimpleReflection 0 * e6RootSimpleReflection 5
  | 1 => e6RootSimpleReflection 2 * e6RootSimpleReflection 4
  | 2 => e6RootSimpleReflection 3
  | 3 => e6RootSimpleReflection 1

/-- Number of E6 simple letters in each displayed generator. -/
def e6FoldedWeylWeight (a : Fin 4) : ℕ :=
  match a with
  | 0 => 2
  | 1 => 2
  | 2 => 1
  | 3 => 1

theorem e6FoldedWeylWeight_pos (a : Fin 4) : 0 < e6FoldedWeylWeight a := by
  fin_cases a <;> decide

/-- Convert a public simple reflection back to its literal lattice formula. -/
theorem e6RootSimpleReflection_coordinates (i : Fin 6) (β : E6Data.Root) :
    ((e6RootSimpleReflection i).val β).val =
      reflection (E6Data.nodeEquiv.symm i) β.val := by
  change E6Data.reflect (E6Data.baseIndexEquiv i).val β.val = _
  rw [E6Data.baseIndexEquiv_apply]
  exact reflect_simpleRoot_coordinates (E6Data.nodeEquiv.symm i) β.val

theorem e6FoldedWeylGenerator_coordinates (a : Fin 4) (β : E6Data.Root) :
    ((e6FoldedWeylGenerator a).val β).val = foldedReflectionLift ℤ a β.val := by
  fin_cases a <;>
    simp only [e6FoldedWeylGenerator, Subgroup.coe_mul, Equiv.Perm.mul_apply,
      e6RootSimpleReflection_coordinates, foldedReflectionLift] <;> rfl

/-- Fixedness is the actual root-permutation commutation equation. -/
theorem e6FoldedWeylGenerator_fixed (a : Fin 4) :
    Function.Commute rootDiagram (e6FoldedWeylGenerator a).val := by
  intro β
  apply Subtype.ext
  change latticeDiagram ℤ ((e6FoldedWeylGenerator a).val β).val = _
  rw [e6FoldedWeylGenerator_coordinates, e6FoldedWeylGenerator_coordinates,
    rootDiagram_val]
  exact foldedReflectionLift_diagram ℤ a β.val

theorem e6FoldedWeylGenerator_mul_self (a : Fin 4) :
    e6FoldedWeylGenerator a * e6FoldedWeylGenerator a = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro β
  apply Subtype.ext
  change ((e6FoldedWeylGenerator a).val ((e6FoldedWeylGenerator a).val β)).val = β.val
  rw [e6FoldedWeylGenerator_coordinates, e6FoldedWeylGenerator_coordinates]
  exact foldedReflectionLift_involutive ℤ a β.val

theorem e6RootWeyl_diagramFixed_mul (w v : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val)
    (hv : Function.Commute rootDiagram v.val) :
    Function.Commute rootDiagram (w * v).val := by
  intro β
  change rootDiagram (w.val (v.val β)) = w.val (v.val (rootDiagram β))
  rw [hw (v.val β), hv β]

/-- A nonidentity fixed Weyl permutation admits a fixed right descent of weight
one or two. At nodes 4 and 5 use the partner descent at 2 and 0 respectively. -/
theorem e6RootWeyl_exists_foldedDescent (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) (hne : w ≠ 1) :
    ∃ a : Fin 4,
      Function.Commute rootDiagram (w * e6FoldedWeylGenerator a).val ∧
      rootWeylLength E6Data.pairing E6Data.base (w * e6FoldedWeylGenerator a) +
          e6FoldedWeylWeight a = rootWeylLength E6Data.pairing E6Data.base w := by
  have h0 (hneg : ¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv 0).val)) :
      rootWeylLength E6Data.pairing E6Data.base (w * e6FoldedWeylGenerator 0) +
          e6FoldedWeylWeight 0 = rootWeylLength E6Data.pairing E6Data.base w := by
    change rootWeylLength E6Data.pairing E6Data.base
      (w * (e6RootSimpleReflection 0 * e6RootSimpleReflection 5)) + 2 = _
    simpa only [show simpleNode (0 : Fin 6) = 5 from rfl, mul_assoc] using
      e6RootWeyl_length_pair_descent w hw 0 (by decide) hneg
  have h2 (hneg : ¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv 2).val)) :
      rootWeylLength E6Data.pairing E6Data.base (w * e6FoldedWeylGenerator 1) +
          e6FoldedWeylWeight 1 = rootWeylLength E6Data.pairing E6Data.base w := by
    change rootWeylLength E6Data.pairing E6Data.base
      (w * (e6RootSimpleReflection 2 * e6RootSimpleReflection 4)) + 2 = _
    simpa only [show simpleNode (2 : Fin 6) = 4 from rfl, mul_assoc] using
      e6RootWeyl_length_pair_descent w hw 2 (by decide) hneg
  obtain ⟨i, hi, hpartner⟩ := e6RootWeyl_exists_simpleDescent_orbit w hw hne
  have hchoose : ∃ a : Fin 4,
      rootWeylLength E6Data.pairing E6Data.base (w * e6FoldedWeylGenerator a) +
          e6FoldedWeylWeight a = rootWeylLength E6Data.pairing E6Data.base w := by
    fin_cases i
    · exact ⟨0, h0 hi⟩
    · refine ⟨3, ?_⟩
      exact rootWeylLength_mul_simple_of_negative E6Data.pairing E6Data.base
        w (E6Data.baseIndexEquiv 1) hi
    · exact ⟨1, h2 hi⟩
    · refine ⟨2, ?_⟩
      exact rootWeylLength_mul_simple_of_negative E6Data.pairing E6Data.base
        w (E6Data.baseIndexEquiv 3) hi
    · exact ⟨1, h2 hpartner⟩
    · exact ⟨0, h0 hpartner⟩
  obtain ⟨a, ha⟩ := hchoose
  exact ⟨a, e6RootWeyl_diagramFixed_mul w (e6FoldedWeylGenerator a) hw
    (e6FoldedWeylGenerator_fixed a), ha⟩

/-- Evaluation takes place in the actual E6 Weyl image. -/
def e6FoldedWeylWord (l : List (Fin 4)) : E6RootWeyl :=
  (l.map e6FoldedWeylGenerator).prod

def e6FoldedWeylWordWeight (l : List (Fin 4)) : ℕ :=
  (l.map e6FoldedWeylWeight).sum

@[simp] theorem e6FoldedWeylWord_nil : e6FoldedWeylWord [] = 1 := rfl

@[simp] theorem e6FoldedWeylWord_cons (a : Fin 4) (l : List (Fin 4)) :
    e6FoldedWeylWord (a :: l) = e6FoldedWeylGenerator a * e6FoldedWeylWord l := by
  simp only [e6FoldedWeylWord, List.map_cons, List.prod_cons]

theorem e6FoldedWeylWord_append_singleton (l : List (Fin 4)) (a : Fin 4) :
    e6FoldedWeylWord (l ++ [a]) = e6FoldedWeylWord l * e6FoldedWeylGenerator a := by
  simp only [e6FoldedWeylWord, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem e6FoldedWeylWordWeight_append_singleton (l : List (Fin 4)) (a : Fin 4) :
    e6FoldedWeylWordWeight (l ++ [a]) =
      e6FoldedWeylWordWeight l + e6FoldedWeylWeight a := by
  simp only [e6FoldedWeylWordWeight, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero]

theorem e6FoldedWeylWord_fixed (l : List (Fin 4)) :
    Function.Commute rootDiagram (e6FoldedWeylWord l).val := by
  induction l with
  | nil => intro β; rfl
  | cons a l ih =>
    rw [e6FoldedWeylWord_cons]
    exact e6RootWeyl_diagramFixed_mul _ _ (e6FoldedWeylGenerator_fixed a) ih

theorem e6FoldedWeylWord_coordinates (l : List (Fin 4)) (β : E6Data.Root) :
    ((e6FoldedWeylWord l).val β).val = foldedRootWordAction l β.val := by
  induction l generalizing β with
  | nil => rfl
  | cons a l ih =>
    rw [e6FoldedWeylWord_cons]
    change ((e6FoldedWeylGenerator a).val ((e6FoldedWeylWord l).val β)).val =
      foldedReflectionLift ℤ a (foldedRootWordAction l β.val)
    exact (e6FoldedWeylGenerator_coordinates a ((e6FoldedWeylWord l).val β)).trans
      (congrArg (foldedReflectionLift ℤ a) (ih β))

/-- Every diagram-fixed actual Weyl permutation has a folded word of total
weight equal to its inherited E6 length. No uniqueness of the word is asserted. -/
theorem e6RootWeyl_exists_foldedWord (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) :
    ∃ l : List (Fin 4), e6FoldedWeylWord l = w ∧
      e6FoldedWeylWordWeight l = rootWeylLength E6Data.pairing E6Data.base w := by
  have aux : ∀ n : ℕ, ∀ v : E6RootWeyl,
      rootWeylLength E6Data.pairing E6Data.base v = n →
      Function.Commute rootDiagram v.val →
      ∃ l : List (Fin 4), e6FoldedWeylWord l = v ∧
        e6FoldedWeylWordWeight l = rootWeylLength E6Data.pairing E6Data.base v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hvn hv
      by_cases hv1 : v = 1
      · subst v
        exact ⟨[], rfl, (rootWeylLength_one E6Data.pairing E6Data.base).symm⟩
      · obtain ⟨a, hnext, hdrop⟩ := e6RootWeyl_exists_foldedDescent v hv hv1
        have hpos := e6FoldedWeylWeight_pos a
        have hlt : rootWeylLength E6Data.pairing E6Data.base
            (v * e6FoldedWeylGenerator a) < n := by omega
        obtain ⟨l, hl, hweight⟩ := ih _ hlt (v * e6FoldedWeylGenerator a) rfl hnext
        refine ⟨l ++ [a], ?_, ?_⟩
        · rw [e6FoldedWeylWord_append_singleton, hl, mul_assoc,
            e6FoldedWeylGenerator_mul_self, mul_one]
        · rw [e6FoldedWeylWordWeight_append_singleton, hweight]
          exact hdrop
  exact aux _ w rfl hw

/-- Generation of the entire diagram-fixed Weyl set, in both directions. -/
theorem e6RootWeyl_diagramFixed_iff_exists_foldedWord (w : E6RootWeyl) :
    Function.Commute rootDiagram w.val ↔
      ∃ l : List (Fin 4), e6FoldedWeylWord l = w := by
  constructor
  · intro hw
    obtain ⟨l, hl, _hweight⟩ := e6RootWeyl_exists_foldedWord w hw
    exact ⟨l, hl⟩
  · rintro ⟨l, rfl⟩
    exact e6FoldedWeylWord_fixed l

section Normalizer

variable (K : Type*) [Field K]

theorem foldedWeylInN_rootAction_eq_e6FoldedWeylGenerator (a : Fin 4) :
    companionNormalizerRootAction K (foldedWeylInN K a) =
      (e6FoldedWeylGenerator a).val := by
  apply Equiv.ext
  intro β
  apply Subtype.ext
  exact (foldedWeylInN_rootAction K a β).trans
    (e6FoldedWeylGenerator_coordinates a β).symm

/-- Equality of the full root permutations, not just their action on a seed. -/
theorem foldedWeylWordInN_rootAction_eq_e6FoldedWeylWord (l : List (Fin 4)) :
    companionNormalizerRootAction K (foldedWeylWordInN K l) =
      (e6FoldedWeylWord l).val := by
  apply Equiv.ext
  intro β
  apply Subtype.ext
  exact (foldedWeylWordInN_rootAction K l β).trans
    (e6FoldedWeylWord_coordinates l β).symm

end Normalizer

section FixedNormalizer

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- A weight-exact folded word with its literal graph--field-fixed normalizer
representative. The constant-parameter representatives need no degree-two premise. -/
theorem e6RootWeyl_exists_fixed_normalizer_word (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) :
    ∃ l : List (Fin 4), e6FoldedWeylWord l = w ∧
      e6FoldedWeylWordWeight l = rootWeylLength E6Data.pairing E6Data.base w ∧
      (foldedWeylWordInN K l).val ∈ companionFixedSubgroup F K ∧
      companionNormalizerRootAction K (foldedWeylWordInN K l) = w.val := by
  obtain ⟨l, hl, hweight⟩ := e6RootWeyl_exists_foldedWord w hw
  refine ⟨l, hl, hweight, foldedWeylWordInN_fixed K F l, ?_⟩
  rw [foldedWeylWordInN_rootAction_eq_e6FoldedWeylWord, hl]

theorem e6RootWeyl_exists_fixed_normalizer_lift (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) :
    ∃ n : CompanionNormalizer K, n.val ∈ companionFixedSubgroup F K ∧
      companionNormalizerRootAction K n = w.val := by
  obtain ⟨l, _hl, _hweight, hfixed, haction⟩ :=
    e6RootWeyl_exists_fixed_normalizer_word F K w hw
  exact ⟨foldedWeylWordInN K l, hfixed, haction⟩

end FixedNormalizer

end Atlas.Chevalley.TwistedE6
