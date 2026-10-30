import FamilyWork.WeylCellTwist

/-! The actual graph--Frobenius fixed group is a disjoint union of its literal
fixed Bruhat cells, indexed by the actual diagram-fixed Weyl permutations.
This gives a weighted-sum expression for its order; evaluation of that Weyl
sum, the full center and simplicity remain separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Classical

/-- Actual fixed Weyl permutations, not a separately chosen abstract F4 group. -/
def E6DiagramFixedWeyl :=
  {w : (rootDatum .E6).pairing.weylGroupToPerm.range // Commute w.val rootDiagram}

instance e6DiagramFixedWeylFinite : Finite E6DiagramFixedWeyl :=
  inferInstanceAs (Finite {w : (rootDatum .E6).pairing.weylGroupToPerm.range //
    Commute w.val rootDiagram})

noncomputable instance e6DiagramFixedWeylFintype : Fintype E6DiagramFixedWeyl :=
  Fintype.ofFinite _

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- A fixed element's unique split-cell label is necessarily diagram fixed. -/
theorem e6FixedWeylCell_index_fixed
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (g : e6FixedWeylCell F K w) : Commute w.val rootDiagram := by
  have htw := e6WeylCell_twist_mem F K w g.val g.property.1
  have hg : companionTwist F K g.val = g.val := g.property.2
  rw [hg] at htw
  obtain ⟨v, _, huniq⟩ := existsUnique_mem_positiveWitnessedWeylCell
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts g.val
  have he : e6WeylDiagram w = w := (huniq _ htw).trans (huniq _ g.property.1).symm
  exact (e6WeylDiagram_eq_self_iff w).mp he

/-- Existence and uniqueness on the original fixed group, with no counting argument. -/
theorem e6FixedGroup_existsUnique_cell (g : companionFixedSubgroup F K) :
    ∃! w : E6DiagramFixedWeyl, g.val ∈ e6FixedWeylCell F K w.val := by
  obtain ⟨w, hw, huniq⟩ := existsUnique_mem_positiveWitnessedWeylCell
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts g.val
  have hmem : g.val ∈ e6FixedWeylCell F K w := ⟨hw, g.property⟩
  refine ⟨⟨w, e6FixedWeylCell_index_fixed F K w ⟨g.val, hmem⟩⟩, hmem, ?_⟩
  intro v hv
  exact Subtype.ext (huniq v.val hv.1)

/-- Each fibre is a subset of H through the original inclusion. -/
def e6FixedCellInGroup (w : E6DiagramFixedWeyl) : Set (companionFixedSubgroup F K) :=
  {g | g.val ∈ e6FixedWeylCell F K w.val}

def e6FixedCellInGroupEquiv (w : E6DiagramFixedWeyl) :
    e6FixedCellInGroup F K w ≃ e6FixedWeylCell F K w.val where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, g.property.2⟩, g.property⟩
  left_inv g := rfl
  right_inv g := rfl

/-- The disjoint union of the literal fixed fibres is H itself. -/
def e6FixedBruhatEquiv :
    (Σ w : E6DiagramFixedWeyl, e6FixedCellInGroup F K w) ≃ companionFixedSubgroup F K :=
  Set.sigmaEquiv (e6FixedCellInGroup F K) (e6FixedGroup_existsUnique_cell F K)

@[simp] theorem e6FixedBruhatEquiv_val
    (x : Σ w : E6DiagramFixedWeyl, e6FixedCellInGroup F K w) :
    (e6FixedBruhatEquiv F K x).val = x.2.val.val := rfl

/-- Every coordinate factor and representative belongs to the actual fixed group. -/
def e6FixedBruhatCoordinatesEquiv :
    (Σ w : E6DiagramFixedWeyl,
      e6CellInversionFixedSubgroup F K w.val × companionFixedBorel F K) ≃
      companionFixedSubgroup F K :=
  (Equiv.sigmaCongrRight (fun w : E6DiagramFixedWeyl =>
    (e6FixedWeylCellParameterEquiv F K w.val w.property).trans
      (e6FixedCellInGroupEquiv F K w).symm)).trans (e6FixedBruhatEquiv F K)

/-- An order expression with its still unevaluated, literal weighted Weyl sum. -/
theorem companionFixedSubgroup_card_weightedSum (hdeg : Module.finrank F K = 2) :
    Nat.card (companionFixedSubgroup F K) =
      (∑ w : E6DiagramFixedWeyl,
        Nat.card F ^ RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w.val) *
      (Nat.card F ^ 36 * (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2) := by
  calc
    _ = Nat.card (Σ w : E6DiagramFixedWeyl, e6FixedCellInGroup F K w) :=
      (Nat.card_congr (e6FixedBruhatEquiv F K)).symm
    _ = ∑ w : E6DiagramFixedWeyl, Nat.card (e6FixedCellInGroup F K w) := Nat.card_sigma
    _ = ∑ w : E6DiagramFixedWeyl,
        Nat.card F ^ RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w.val *
          (Nat.card F ^ 36 * (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Nat.card_congr (e6FixedCellInGroupEquiv F K w),
        e6FixedWeylCell_card F K w.val w.property hdeg]
    _ = _ := (Finset.sum_mul _ _ _).symm

end Atlas.Chevalley.TwistedE6
