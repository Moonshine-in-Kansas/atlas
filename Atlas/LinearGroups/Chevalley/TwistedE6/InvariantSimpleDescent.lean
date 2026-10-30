import Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates
import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedWeylRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.ReducedWordFirstDescent
import Atlas.LinearGroups.Chevalley.RootData.TwoDescentSuffix

/-!
Verification receipts are recorded separately.

Small prerequisites for invariant simple-descent induction in the actual E6
root-permutation Weyl image. No full fixed-Weyl generation, F4 recognition,
weighted sum, normalizer quotient, or Bruhat statement is declared here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- A nonidentity actual Weyl permutation has a right simple descent.
Apply the inherited first-letter result to a minimum word for the inverse. -/
theorem rootWeyl_exists_simple_descent_of_ne_one
    (w : P.weylGroupToPerm.range) (hw : w ≠ 1) :
    ∃ i : b.support, ¬ b.IsPos (w.val i.val) := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w⁻¹
  cases l with
  | nil =>
    have hwi : w⁻¹ = 1 := by
      apply Subtype.ext
      change (w⁻¹).val = (1 : Equiv.Perm ι)
      exact hl.symm.trans (simpleReflectionWord_nil P b)
    exact False.elim (hw (by simpa only [inv_eq_one] using hwi))
  | cons i l =>
    have hword : rootWeylWord P b (i :: l) = w⁻¹ := by
      apply Subtype.ext
      exact (rootWeylWord_val P b (i :: l)).trans hl
    have hred : IsReducedRootWord P b (i :: l) := by
      change rootWeylLength P b (rootWeylWord P b (i :: l)) = (i :: l).length
      rw [hword]
      exact hlen.symm
    have hneg := rootWeylWord_inverse_first_negative P b i l hred
    rw [hword, inv_inv] at hneg
    exact ⟨i, hneg⟩

end Atlas.Chevalley.RootData

namespace Atlas.Chevalley.TwistedE6

open Classical RootData

local instance invariantDescentRootFintype : Fintype E6Data.Root := Fintype.ofFinite _

/-- The full inherited root-permutation Weyl image, before taking diagram fixed points. -/
abbrev E6RootWeyl := E6Data.pairing.weylGroupToPerm.range

/-- Public simple-node indexing, as in the companion APIs. -/
def e6RootSimpleReflection (i : Fin 6) : E6RootWeyl :=
  simpleWeylReflection E6Data.pairing E6Data.base (E6Data.baseIndexEquiv i)

theorem e6_rootDiagram_isPos_iff (β : E6Data.Root) :
    E6Data.base.IsPos (rootDiagram β) ↔ E6Data.base.IsPos β := by
  simp only [e6_isPos_iff_coordinates_nonnegative, rootDiagram_val, latticeDiagram_apply]
  constructor
  · intro h j
    simpa only [latticeNode_involutive j] using h (latticeNode j)
  · intro h j
    exact h (latticeNode j)

theorem e6_rootDiagram_baseIndex (i : Fin 6) :
    rootDiagram (E6Data.baseIndexEquiv i).val =
      (E6Data.baseIndexEquiv (simpleNode i)).val := by
  calc
    rootDiagram (E6Data.baseIndexEquiv i).val =
        (baseDiagram (E6Data.baseIndexEquiv i)).val :=
      (baseDiagram_root (E6Data.baseIndexEquiv i)).symm
    _ = (E6Data.baseIndexEquiv (simpleNode i)).val :=
      congrArg Subtype.val (baseDiagram_index i)

/-- The right simple-descent set of a diagram-fixed Weyl element is invariant. -/
theorem e6RootWeyl_simpleDescent_diagram_iff (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) (i : Fin 6) :
    (¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv (simpleNode i)).val)) ↔
      ¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv i).val) := by
  have hi := hw (E6Data.baseIndexEquiv i).val
  rw [e6_rootDiagram_baseIndex] at hi
  rw [← hi, e6_rootDiagram_isPos_iff]

/-- A nonidentity diagram-fixed element has an entire descending simple orbit. -/
theorem e6RootWeyl_exists_simpleDescent_orbit (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) (hne : w ≠ 1) :
    ∃ i : Fin 6,
      (¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv i).val)) ∧
      ¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv (simpleNode i)).val) := by
  obtain ⟨j, hj⟩ :=
    rootWeyl_exists_simple_descent_of_ne_one E6Data.pairing E6Data.base w hne
  obtain ⟨i, rfl⟩ := E6Data.baseIndexEquiv.surjective j
  exact ⟨i, hj, (e6RootWeyl_simpleDescent_diagram_iff w hw i).mpr hj⟩

/-- A moved descending simple orbit removes exactly two existing E6 letters.
The other negative image follows from diagram invariance; orthogonality is inherited. -/
theorem e6RootWeyl_length_pair_descent (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) (i : Fin 6)
    (hmoved : simpleNode i ≠ i)
    (hi : ¬ E6Data.base.IsPos (w.val (E6Data.baseIndexEquiv i).val)) :
    rootWeylLength E6Data.pairing E6Data.base
        (w * e6RootSimpleReflection i * e6RootSimpleReflection (simpleNode i)) + 2 =
      rootWeylLength E6Data.pairing E6Data.base w := by
  have hmoved' : simpleNode (simpleNode i) ≠ simpleNode i := by
    simpa only [simpleNode_involutive i] using Ne.symm hmoved
  have hji : E6Data.base.cartanMatrix (E6Data.baseIndexEquiv (simpleNode i))
      (E6Data.baseIndexEquiv i) = 0 := simpleNode_moved_cartan i hmoved
  have hij : E6Data.base.cartanMatrix (E6Data.baseIndexEquiv i)
      (E6Data.baseIndexEquiv (simpleNode i)) = 0 := by
    have h := simpleNode_moved_cartan (simpleNode i) hmoved'
    rw [simpleNode_involutive i] at h
    exact h
  exact rootWeylLength_two_descents_two E6Data.pairing E6Data.base w
    (E6Data.baseIndexEquiv i) (E6Data.baseIndexEquiv (simpleNode i)) hij hji hi
    ((e6RootWeyl_simpleDescent_diagram_iff w hw i).mpr hi)

/-- The existing actual folded representatives act by diagram-commuting root
permutations. This supplies one side of the later fixed-Weyl generation argument. -/
theorem foldedWeylInN_rootAction_commute_diagram (K : Type*) [Field K] (i : Fin 4) :
    Function.Commute rootDiagram (companionNormalizerRootAction K (foldedWeylInN K i)) := by
  intro β
  apply Subtype.ext
  change latticeDiagram ℤ
    ((companionNormalizerRootAction K (foldedWeylInN K i) β).val) = _
  rw [foldedWeylInN_rootAction, foldedWeylInN_rootAction, rootDiagram_val]
  exact foldedReflectionLift_diagram ℤ i β.val

end Atlas.Chevalley.TwistedE6
