import FamilyWork.FixedWeylCell

/-! Graph--field covariance of the actual split E6 Bruhat cells. The proof
transports actual simple normalizer words and uses disjointness of the existing
split cells. No order formula or fixed-group generation premise is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Classical RootData Atlas.GroupTheory.ReducedWords

/-- Diagram transport of the entire actual root-word action. -/
theorem e6RootWeylWord_diagram (l : List E6Data.base.support) (β : E6Data.Root) :
    (rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base (l.map baseDiagram)).val
        (rootDiagram β) =
      rootDiagram ((rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base l).val β) := by
  induction l generalizing β with
  | nil => rfl
  | cons i l ih =>
    change E6Data.reflectionPerm (baseDiagram i).val
      ((rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base (l.map baseDiagram)).val
        (rootDiagram β)) =
      rootDiagram (E6Data.reflectionPerm i.val
        ((rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base l).val β))
    rw [ih, baseDiagram_root]
    exact (rootDiagram_reflectionPerm _ _).symm

/-- The actual diagram conjugate lies in the same Weyl image by word transport. -/
def e6WeylDiagram (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    (rootDatum .E6).pairing.weylGroupToPerm.range := by
  let l := (root_reduced_representatives (rootDatum .E6).pairing (rootDatum .E6).base w).choose
  have hl : rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base l = w :=
    (root_reduced_representatives (rootDatum .E6).pairing (rootDatum .E6).base w).choose_spec.1
  refine ⟨rootDiagram.trans (w.val.trans rootDiagram), ?_⟩
  have he : rootDiagram.trans (w.val.trans rootDiagram) =
      (rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base (l.map baseDiagram)).val := by
    apply Equiv.ext
    intro β
    have h := e6RootWeylWord_diagram l (rootDiagram β)
    rw [rootDiagram_involutive, hl] at h
    exact h.symm
  rw [he]
  exact (rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base (l.map baseDiagram)).property

@[simp] theorem e6WeylDiagram_val (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (β : E6Data.Root) :
    (e6WeylDiagram w).val β = rootDiagram (w.val (rootDiagram β)) := rfl

theorem e6WeylDiagram_eq_self_iff (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    e6WeylDiagram w = w ↔ Commute w.val rootDiagram := by
  constructor
  · intro h
    apply Equiv.ext
    intro β
    change E6Data.Root at β
    change w.val (rootDiagram β) = rootDiagram (w.val β)
    have he := congrArg (fun x : (rootDatum .E6).pairing.weylGroupToPerm.range =>
      x.val (rootDiagram β)) h
    change rootDiagram (w.val (rootDiagram (rootDiagram β))) = w.val (rootDiagram β) at he
    rw [rootDiagram_involutive] at he
    exact he.symm
  · intro h
    apply Subtype.ext
    apply Equiv.ext
    intro β
    change E6Data.Root at β
    change rootDiagram (w.val (rootDiagram β)) = w.val β
    have hc : w.val (rootDiagram β) = rootDiagram (w.val β) :=
      congrArg (fun f : Equiv.Perm E6Data.Root => f β) h.eq
    exact (congrArg rootDiagram hc).trans (rootDiagram_involutive _)

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def e6SimpleNormalizerWord (l : List E6Data.base.support) : CompanionNormalizer K :=
  wordEval (weightCompanionSimpleWeylInN
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K) l

theorem e6SimpleNormalizerWord_rootAction (l : List E6Data.base.support) :
    companionNormalizerRootAction K (e6SimpleNormalizerWord K l) =
      (rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base l).val :=
  weightCompanionNRootPermHom_wordEval
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K l

/-- The twist transports the literal word, with no hypothetical lift selection. -/
theorem companionTwist_e6SimpleNormalizerWord (l : List E6Data.base.support) :
    companionTwist F K (e6SimpleNormalizerWord K l).val =
      (e6SimpleNormalizerWord K (l.map baseDiagram)).val := by
  induction l with
  | nil => exact map_one (companionTwist F K)
  | cons i l ih =>
    obtain ⟨j, rfl⟩ := E6Data.baseIndexEquiv.surjective i
    change companionTwist F K (simpleWeyl K j * (e6SimpleNormalizerWord K l).val) =
      (weightCompanionSimpleWeylInN
        (rootDatum .E6).pairing (rootDatum .E6).base
        (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
        (selectedWeightOrbits_minuscule .E6) K
        (baseDiagram (E6Data.baseIndexEquiv j))).val *
          (e6SimpleNormalizerWord K (l.map baseDiagram)).val
    rw [map_mul, companionTwist_simpleWeyl, ih, baseDiagram_index]
    rfl

/-- Covariance of the literal cell follows by transporting its two B factors. -/
theorem e6WeylCell_twist_mem (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (g : SelectedWeightCompanion .E6 K)
    (hg : g ∈ positiveWitnessedWeylCell
      (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K w) :
    companionTwist F K g ∈ positiveWitnessedWeylCell
      (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K (e6WeylDiagram w) := by
  let l := (root_reduced_representatives (rootDatum .E6).pairing (rootDatum .E6).base w).choose
  have hl : rootWeylWord (rootDatum .E6).pairing (rootDatum .E6).base l = w :=
    (root_reduced_representatives (rootDatum .E6).pairing (rootDatum .E6).base w).choose_spec.1
  have hn : companionNormalizerRootAction K (e6SimpleNormalizerWord K (l.map baseDiagram)) =
      (e6WeylDiagram w).val := by
    rw [e6SimpleNormalizerWord_rootAction]
    apply Equiv.ext
    intro β
    have h := e6RootWeylWord_diagram l (rootDiagram β)
    rw [rootDiagram_involutive, hl] at h
    exact h
  have hcell := positiveWitnessedWeylCell_eq_of_lift
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts
    (e6WeylDiagram w) (e6SimpleNormalizerWord K (l.map baseDiagram)) hn
  rw [← hcell]
  obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mem_doubleCoset.mp hg
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨companionTwist F K a, e6PositiveTorusJoin_twist_mem F K a ha,
    companionTwist F K b, e6PositiveTorusJoin_twist_mem F K b hb, ?_⟩
  change companionTwist F K g = _
  rw [he, map_mul, map_mul]
  change companionTwist F K a * companionTwist F K (e6SimpleNormalizerWord K l).val *
    companionTwist F K b = _
  rw [companionTwist_e6SimpleNormalizerWord]

end Atlas.Chevalley.TwistedE6
