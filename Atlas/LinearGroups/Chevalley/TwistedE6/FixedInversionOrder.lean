import Atlas.LinearGroups.Chevalley.TwistedE6.InversionCoordinates
import Atlas.LinearGroups.Chevalley.TwistedE6.FixedSubsetParameters
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootInversionCardinality

/-! Full fixed parts of the actual inversion subgroups in E6 Bruhat cells.
The unique compatible orbit product restricts exactly to the inherited subgroup
and to graph--Frobenius fixed points. For a diagram-invariant actual Weyl element
the resulting count is q to its E6 length, including the empty inversion set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

/-- Actual reindexing of the inversion roots by their positive labels. -/
def e6CellInversionLabelEquiv
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    e6CellInversionLabels w ≃ e6CellInversionRoots w where
  toFun i := ⟨e6PositiveRootEquiv i.val, i.property⟩
  invFun β := ⟨e6PositiveRootEquiv.symm β.val, by
    change e6PositiveRootEquiv (e6PositiveRootEquiv.symm β.val) ∈ e6CellInversionRoots w
    rw [Equiv.apply_symm_apply]
    exact β.property⟩
  left_inv i := Subtype.ext (Equiv.symm_apply_apply e6PositiveRootEquiv i.val)
  right_inv β := Subtype.ext (Equiv.apply_symm_apply e6PositiveRootEquiv β.val)

theorem e6CellInversionLabels_card
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    Nat.card (e6CellInversionLabels w) =
      RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w := by
  calc
    _ = Nat.card (e6CellInversionRoots w) := Nat.card_congr (e6CellInversionLabelEquiv w)
    _ = RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w⁻¹ :=
      RootData.positiveRootInversionSubset_card (rootDatum .E6).pairing (rootDatum .E6).base w⁻¹
    _ = _ := RootData.rootWeylLength_inv (rootDatum .E6).pairing (rootDatum .E6).base w

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Multiply the same supported compatible coordinates in the original group. -/
def e6FixedInversionProduct (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (s : PositiveDiagramParameters.SubsetFixedFunctions F K (e6CellInversionLabels w)) :
    e6CellInversionFixedSubgroup F K w :=
  ⟨(e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s.val).val,
    (e6OrbitLiftProduct_mem_inversion_iff K w s.val).mpr s.property.2,
    (compatiblePositiveProduct_fixed_iff K F hdeg s.val).mpr s.property.1⟩

@[simp] theorem e6FixedInversionProduct_val (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (s : PositiveDiagramParameters.SubsetFixedFunctions F K (e6CellInversionLabels w)) :
    (e6FixedInversionProduct F K hdeg w s).val =
      (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s.val).val := rfl

theorem e6FixedInversionProduct_injective (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    Function.Injective (e6FixedInversionProduct F K hdeg w) := by
  intro s t h
  apply Subtype.ext
  apply e6OrbitLiftProduct_injective K (e6CompatiblePositiveRootLift K)
  apply Subtype.ext
  exact congrArg (fun g : e6CellInversionFixedSubgroup F K w => g.val) h

/-- Every fixed element of the entire inherited inversion subgroup is recovered. -/
theorem e6FixedInversionProduct_surjective (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    Function.Surjective (e6FixedInversionProduct F K hdeg w) := by
  intro g
  let u : e6CellInversionSubgroup K w := ⟨g.val, g.property.1⟩
  obtain ⟨s, hs⟩ := e6InversionProduct_surjective K w u
  have hval : (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s.val).val = g.val :=
    congrArg (fun x : e6CellInversionSubgroup K w => x.val) hs
  have hfixed : (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s.val).val ∈
      companionFixedSubgroup F K := by
    rw [hval]
    exact g.property.2
  let t : PositiveDiagramParameters.SubsetFixedFunctions F K (e6CellInversionLabels w) :=
    ⟨s.val, (compatiblePositiveProduct_fixed_iff K F hdeg s.val).mp hfixed, s.property⟩
  exact ⟨t, Subtype.ext hval⟩

/-- This set normal form has no invariant-Weyl premise; that premise is needed
only when counting the supported compatible parameter space. -/
def e6FixedInversionProductEquiv (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range) :
    PositiveDiagramParameters.SubsetFixedFunctions F K (e6CellInversionLabels w) ≃
      e6CellInversionFixedSubgroup F K w :=
  Equiv.ofBijective (e6FixedInversionProduct F K hdeg w)
    ⟨e6FixedInversionProduct_injective F K hdeg w,
      e6FixedInversionProduct_surjective F K hdeg w⟩

@[simp] theorem e6FixedInversionProductEquiv_apply (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (s : PositiveDiagramParameters.SubsetFixedFunctions F K (e6CellInversionLabels w)) :
    e6FixedInversionProductEquiv F K hdeg w s = e6FixedInversionProduct F K hdeg w s := rfl

/-- Uniform fixed inversion order, under exactly diagram invariance and a finite
quadratic extension; no full group, Borel or split-subgroup order is an input. -/
theorem e6CellInversionFixedSubgroup_card (hdeg : Module.finrank F K = 2)
    (w : (rootDatum .E6).pairing.weylGroupToPerm.range)
    (hw : Commute w.val rootDiagram) :
    Nat.card (e6CellInversionFixedSubgroup F K w) =
      Nat.card F ^ RootData.rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w := by
  calc
    _ = Nat.card (PositiveDiagramParameters.SubsetFixedFunctions F K (e6CellInversionLabels w)) :=
      (Nat.card_congr (e6FixedInversionProductEquiv F K hdeg w)).symm
    _ = Nat.card F ^ Nat.card (e6CellInversionLabels w) :=
      PositiveDiagramParameters.subsetFixedFunctions_card F K (e6CellInversionLabels w)
        (fun i hi => (e6CellInversionLabels_diagram_iff w hw i).mpr hi) hdeg
    _ = _ := congrArg (fun n : ℕ => Nat.card F ^ n) (e6CellInversionLabels_card w)

end Atlas.Chevalley.TwistedE6
