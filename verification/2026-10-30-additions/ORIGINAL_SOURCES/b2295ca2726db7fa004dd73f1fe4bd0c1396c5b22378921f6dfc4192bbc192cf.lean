import FamilyWork.FixedCellCoordinates

/-! Each diagram-fixed Weyl permutation has an actual fixed representative,
and its literal split Bruhat cell intersected with H has the expected order.
Coverage of H and evaluation of the weighted Weyl sum are separate obligations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
  (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
  (hw : Commute w.val rootDiagram)

include hw in
/-- Convert multiplication of permutations to the convention of folded generation. -/
theorem e6Weyl_commute_function : Function.Commute rootDiagram w.val := by
  intro x
  exact congrArg (fun f : Equiv.Perm E6Data.Root => f x) hw.eq.symm

/-- Choice from a proved existence theorem for the actual normalizer subgroup. -/
def e6FixedNormalizerLift : CompanionNormalizer K :=
  (e6RootWeyl_exists_fixed_normalizer_lift F K w (e6Weyl_commute_function w hw)).choose

theorem e6FixedNormalizerLift_fixed :
    (e6FixedNormalizerLift F K w hw).val ∈ companionFixedSubgroup F K :=
  (e6RootWeyl_exists_fixed_normalizer_lift F K w (e6Weyl_commute_function w hw)).choose_spec.1

theorem e6FixedNormalizerLift_rootAction :
    companionNormalizerRootAction K (e6FixedNormalizerLift F K w hw) = w.val :=
  (e6RootWeyl_exists_fixed_normalizer_lift F K w (e6Weyl_commute_function w hw)).choose_spec.2

/-- The original actual split cell, intersected with H, independent of choices. -/
def e6FixedWeylCell : Set (SelectedWeightCompanion .E6 K) :=
  positiveWitnessedWeylCell (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K w ∩ companionFixedSubgroup F K

theorem e6FixedLiftCell_eq_fixedWeylCell :
    e6FixedLiftCell F K (e6FixedNormalizerLift F K w hw) = e6FixedWeylCell F K w := by
  unfold e6FixedLiftCell e6FixedWeylCell
  exact congrArg (fun S : Set (SelectedWeightCompanion .E6 K) =>
    S ∩ (companionFixedSubgroup F K : Set (SelectedWeightCompanion .E6 K)))
    (positiveWitnessedWeylCell_eq_of_lift
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts w
    (e6FixedNormalizerLift F K w hw) (e6FixedNormalizerLift_rootAction F K w hw))

/-- Actual coordinates on the literal fixed cell. -/
def e6FixedWeylCellParameterEquiv :
    (e6CellInversionFixedSubgroup F K w × companionFixedBorel F K) ≃
      e6FixedWeylCell F K w :=
  (e6FixedLiftCellParameterEquiv F K w hw (e6FixedNormalizerLift F K w hw)
    (e6FixedNormalizerLift_rootAction F K w hw) (e6FixedNormalizerLift_fixed F K w hw)).trans
    (Equiv.setCongr (e6FixedLiftCell_eq_fixedWeylCell F K w hw))

@[simp] theorem e6FixedWeylCellParameterEquiv_val
    (p : e6CellInversionFixedSubgroup F K w × companionFixedBorel F K) :
    (e6FixedWeylCellParameterEquiv F K w hw p).val =
      p.1.val * (e6FixedNormalizerLift F K w hw).val * p.2.val := rfl

include hw in
/-- The cell order uses the newly proved fixed inversion and Borel counts. -/
theorem e6FixedWeylCell_card (hdeg : Module.finrank F K = 2) :
    Nat.card (e6FixedWeylCell F K w) =
      Nat.card F ^ RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w *
        (Nat.card F ^ 36 * (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2) := by
  rw [← Nat.card_congr (e6FixedWeylCellParameterEquiv F K w hw), Nat.card_prod,
    e6CellInversionFixedSubgroup_card F K hdeg w hw, companionFixedBorel_card F K hdeg]

end Atlas.Chevalley.TwistedE6
