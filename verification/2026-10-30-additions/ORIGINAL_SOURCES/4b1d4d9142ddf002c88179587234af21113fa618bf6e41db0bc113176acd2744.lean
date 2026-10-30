import FamilyWork.WitnessedSubsetCoordinates
import FamilyWork.InversionCarrier

/-! Exact supported coordinates on the inherited E6 left-cell inversion subgroup.
The product uses the already proved compatible root lifts and orbit ordering.
This file identifies the full subgroup, rather than defining it as a product
image. Cardinality and graph-fixed restriction are subsequent steps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

/-- Positive labels made negative by w inverse, retaining the left-cell convention. -/
def e6CellInversionLabels (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    Set (Fin 36) := {i | e6PositiveRootEquiv i ∈ e6CellInversionRoots w}

theorem e6CellInversionLabels_diagram_iff
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (hw : Commute w.val rootDiagram) (i : Fin 36) :
    positiveDiagram i ∈ e6CellInversionLabels w ↔ i ∈ e6CellInversionLabels w := by
  change e6PositiveRootEquiv (positiveDiagram i) ∈ e6CellInversionRoots w ↔
    e6PositiveRootEquiv i ∈ e6CellInversionRoots w
  rw [← e6PositiveRootDiagram_equiv]
  exact e6CellInversionRoots_diagram_iff w hw (e6PositiveRootEquiv i)

variable (K : Type*) [Field K]

/-- The complete compatible product belongs to U_w precisely when its other
coordinates vanish. All collection and ordering hypotheses are discharged here. -/
theorem e6OrbitLiftProduct_mem_inversion_iff
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) (s : Fin 36 → K) :
    (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val ∈
        e6CellInversionSubgroup K w ↔
      ∀ i, i ∉ e6CellInversionLabels w → s i = 0 := by
  have h := positiveRootWitnessedProduct_mem_subset_iff
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (e6CompatiblePositiveRootLift K)
    E6Data.simpleDiamondProducts (e6CellInversionRoots w)
    (e6CellInversionRoots_coneClosed w) e6PositiveRootOrbitOrder
    e6PositiveRootOrbitOrder_nodup e6PositiveRootOrbitOrder_pairwise_height
    mem_e6PositiveRootOrbitOrder (e6PositiveParameterEquiv K s)
  change (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val ∈
      e6CellInversionSubgroup K w ↔
    ∀ β, β ∉ e6CellInversionRoots w → (e6PositiveParameterEquiv K s) β = 0 at h
  rw [h]
  constructor
  · intro hs i hi
    have he := hs (e6PositiveRootEquiv i) hi
    change s (e6PositiveRootEquiv.symm (e6PositiveRootEquiv i)) = 0 at he
    simpa only [Equiv.symm_apply_apply] using he
  · intro hs β hβ
    apply hs (e6PositiveRootEquiv.symm β)
    change e6PositiveRootEquiv (e6PositiveRootEquiv.symm β) ∉ e6CellInversionRoots w
    simpa only [Equiv.apply_symm_apply] using hβ

/-- Supported coordinates; no Frobenius constraint is imposed yet. -/
def e6SupportedInversionCoordinates
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :=
  {s : Fin 36 → K // ∀ i, i ∉ e6CellInversionLabels w → s i = 0}

/-- The original compatible multiplication map, restricted to the actual subgroup. -/
def e6InversionProduct (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (s : e6SupportedInversionCoordinates K w) : e6CellInversionSubgroup K w :=
  ⟨(e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s.val).val,
    (e6OrbitLiftProduct_mem_inversion_iff K w s.val).mpr s.property⟩

@[simp] theorem e6InversionProduct_val
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (s : e6SupportedInversionCoordinates K w) :
    (e6InversionProduct K w s).val =
      (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s.val).val := rfl

theorem e6InversionProduct_injective
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    Function.Injective (e6InversionProduct K w) := by
  intro s t h
  apply Subtype.ext
  apply e6OrbitLiftProduct_injective K (e6CompatiblePositiveRootLift K)
  apply Subtype.ext
  exact congrArg (fun g : e6CellInversionSubgroup K w => g.val) h

theorem e6InversionProduct_surjective
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    Function.Surjective (e6InversionProduct K w) := by
  intro g
  let u : selectedWeightCompanionPositiveSubgroup .E6 K :=
    ⟨g.val, e6CellInversionSubgroup_le_positive K w g.property⟩
  obtain ⟨s, hs⟩ := e6OrbitLiftProduct_surjective K (e6CompatiblePositiveRootLift K) u
  have hval : (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val = g.val :=
    congrArg (fun x : selectedWeightCompanionPositiveSubgroup .E6 K => x.val) hs
  have hmem : (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val ∈
      e6CellInversionSubgroup K w := by
    rw [hval]
    exact g.property
  refine ⟨⟨s, (e6OrbitLiftProduct_mem_inversion_iff K w s).mp hmem⟩, ?_⟩
  exact Subtype.ext hval

/-- Unique supported normal form for every element of the existing inversion group. -/
def e6InversionProductEquiv
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    e6SupportedInversionCoordinates K w ≃ e6CellInversionSubgroup K w :=
  Equiv.ofBijective (e6InversionProduct K w)
    ⟨e6InversionProduct_injective K w, e6InversionProduct_surjective K w⟩

@[simp] theorem e6InversionProductEquiv_apply
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (s : e6SupportedInversionCoordinates K w) :
    e6InversionProductEquiv K w s = e6InversionProduct K w s := rfl

end Atlas.Chevalley.TwistedE6
