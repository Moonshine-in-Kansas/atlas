import FamilyWork.LiftCellCoordinates
import FamilyWork.FixedBorel
import FamilyWork.FixedInversionOrder
import FamilyWork.FoldedWeylGeneration
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellDecomposition

/-! Literal fixed double cells. Uniqueness in the existing split cell forces
both complete coordinates of a fixed element to be fixed, once the normalizer
representative itself is fixed. The representative is supplied by the proved
folded-word construction. No whole-group count or simplicity is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

section Split
variable (K : Type*) [Field K]
  (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
  (n : CompanionNormalizer K)

/-- Actual multiplication with the supplied normalizer representative. -/
def e6LiftCellParameterMap :
    e6CellInversionSubgroup K w × selectedWeightCompanionPositiveTorusJoin .E6 K →
      ↥(DoubleCoset.doubleCoset n.val
        (selectedWeightCompanionPositiveTorusJoin .E6 K)
        (selectedWeightCompanionPositiveTorusJoin .E6 K)) :=
  positiveWitnessedLiftCellParameterMap
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K w n

theorem e6LiftCellParameterMap_injective
    (hn : companionNormalizerRootAction K n = w.val) :
    Function.Injective (e6LiftCellParameterMap K w n) :=
  positiveWitnessedLiftCellParameterMap_injective
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K w n E6Data.simpleDiamondProducts hn

theorem e6LiftCellParameterMap_surjective [Finite K]
    (hn : companionNormalizerRootAction K n = w.val) :
    Function.Surjective (e6LiftCellParameterMap K w n) :=
  positiveWitnessedLiftCellParameterMap_surjective
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K w n E6Data.simpleDiamondProducts hn
end Split

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
  (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
  (hw : Commute w.val rootDiagram)
  (n : CompanionNormalizer K)
  (hn : companionNormalizerRootAction K n = w.val)
  (hfixed : n.val ∈ companionFixedSubgroup F K)

include hw hn hfixed in
/-- Fixedness is detected on the two entire coordinates, not their orders. -/
theorem e6LiftCellProduct_fixed_iff
    (u : e6CellInversionSubgroup K w)
    (b : selectedWeightCompanionPositiveTorusJoin .E6 K) :
    u.val * n.val * b.val ∈ companionFixedSubgroup F K ↔
      u.val ∈ companionFixedSubgroup F K ∧ b.val ∈ companionFixedSubgroup F K := by
  constructor
  · intro hg
    let u' : e6CellInversionSubgroup K w :=
      ⟨companionTwist F K u.val, e6CellInversionSubgroup_twist_mem F K w hw _ u.property⟩
    let b' : selectedWeightCompanionPositiveTorusJoin .E6 K :=
      ⟨companionTwist F K b.val, e6PositiveTorusJoin_twist_mem F K _ b.property⟩
    have hn' : companionTwist F K n.val = n.val := hfixed
    have he : e6LiftCellParameterMap K w n (u', b') =
        e6LiftCellParameterMap K w n (u, b) := by
      apply Subtype.ext
      change companionTwist F K u.val * n.val * companionTwist F K b.val =
        u.val * n.val * b.val
      change companionTwist F K (u.val * n.val * b.val) = u.val * n.val * b.val at hg
      simpa only [map_mul, hn'] using hg
    have hp := e6LiftCellParameterMap_injective K w n hn he
    constructor
    · exact congrArg (fun p : e6CellInversionSubgroup K w ×
        selectedWeightCompanionPositiveTorusJoin .E6 K => p.1.val) hp
    · exact congrArg (fun p : e6CellInversionSubgroup K w ×
        selectedWeightCompanionPositiveTorusJoin .E6 K => p.2.val) hp
  · rintro ⟨hu, hb⟩
    exact (companionFixedSubgroup F K).mul_mem
      ((companionFixedSubgroup F K).mul_mem hu hfixed) hb

/-- Literal intersection of the split double cell with the actual fixed group. -/
def e6FixedLiftCell : Set (SelectedWeightCompanion .E6 K) :=
  DoubleCoset.doubleCoset n.val
    (selectedWeightCompanionPositiveTorusJoin .E6 K)
    (selectedWeightCompanionPositiveTorusJoin .E6 K) ∩ companionFixedSubgroup F K

/-- Multiplication into that literal set from the two full fixed subgroups. -/
def e6FixedLiftCellParameterMap :
    e6CellInversionFixedSubgroup F K w × companionFixedBorel F K →
      e6FixedLiftCell F K n := fun p =>
  ⟨p.1.val * n.val * p.2.val,
    (e6LiftCellParameterMap K w n (⟨p.1.val, p.1.property.1⟩,
      ⟨p.2.val, p.2.property.1⟩)).property,
    (companionFixedSubgroup F K).mul_mem
      ((companionFixedSubgroup F K).mul_mem p.1.property.2 hfixed) p.2.property.2⟩

include hn in
theorem e6FixedLiftCellParameterMap_injective :
    Function.Injective (e6FixedLiftCellParameterMap F K w n hfixed) := by
  intro p q hpq
  have he : e6LiftCellParameterMap K w n
      (⟨p.1.val, p.1.property.1⟩, ⟨p.2.val, p.2.property.1⟩) =
    e6LiftCellParameterMap K w n
      (⟨q.1.val, q.1.property.1⟩, ⟨q.2.val, q.2.property.1⟩) :=
    Subtype.ext (congrArg (fun g : e6FixedLiftCell F K n => g.val) hpq)
  have h := e6LiftCellParameterMap_injective K w n hn he
  exact Prod.ext
    (Subtype.ext (congrArg (fun x : e6CellInversionSubgroup K w ×
      selectedWeightCompanionPositiveTorusJoin .E6 K => x.1.val) h))
    (Subtype.ext (congrArg (fun x : e6CellInversionSubgroup K w ×
      selectedWeightCompanionPositiveTorusJoin .E6 K => x.2.val) h))

include hw hn in
theorem e6FixedLiftCellParameterMap_surjective :
    Function.Surjective (e6FixedLiftCellParameterMap F K w n hfixed) := by
  intro g
  obtain ⟨p, hp⟩ := e6LiftCellParameterMap_surjective K w n hn ⟨g.val, g.property.1⟩
  have hval : p.1.val * n.val * p.2.val = g.val := congrArg Subtype.val hp
  have hf : p.1.val * n.val * p.2.val ∈ companionFixedSubgroup F K := by
    rw [hval]
    exact g.property.2
  have hparts := (e6LiftCellProduct_fixed_iff F K w hw n hn hfixed p.1 p.2).mp hf
  exact ⟨(⟨p.1.val, p.1.property, hparts.1⟩,
    ⟨p.2.val, p.2.property, hparts.2⟩), Subtype.ext hval⟩

/-- A set equivalence, not a claim that a double cell is a group. -/
def e6FixedLiftCellParameterEquiv :
    (e6CellInversionFixedSubgroup F K w × companionFixedBorel F K) ≃
      e6FixedLiftCell F K n :=
  Equiv.ofBijective (e6FixedLiftCellParameterMap F K w n hfixed)
    ⟨e6FixedLiftCellParameterMap_injective F K w n hn hfixed,
      e6FixedLiftCellParameterMap_surjective F K w hw n hn hfixed⟩

@[simp] theorem e6FixedLiftCellParameterEquiv_val
    (p : e6CellInversionFixedSubgroup F K w × companionFixedBorel F K) :
    (e6FixedLiftCellParameterEquiv F K w hw n hn hfixed p).val =
      p.1.val * n.val * p.2.val := rfl

include hw hn hfixed in
theorem e6FixedLiftCell_card (hdeg : Module.finrank F K = 2) :
    Nat.card (e6FixedLiftCell F K n) =
      Nat.card F ^ RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w *
        Nat.card (companionFixedBorel F K) := by
  rw [← Nat.card_congr (e6FixedLiftCellParameterEquiv F K w hw n hn hfixed),
    Nat.card_prod, e6CellInversionFixedSubgroup_card F K hdeg w hw]

end Atlas.Chevalley.TwistedE6
