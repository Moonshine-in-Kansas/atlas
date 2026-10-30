import Atlas.LinearGroups.Chevalley.TwistedE6.FixedWeylFaithfulness
import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedWeylGeneration
import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedLattice
import Atlas.Comparisons.Exceptional.E6.Reflections

/-! Explicit four-coordinate adapter for the literal rational diagram-fixed space.

The base-support coordinates are reindexed by `nodeEquiv.trans baseIndexEquiv`
into the original E6 lattice numbering. The fixed vectors there are exactly
(a,b,c,b,a,d). The resulting rational linear equivalence intertwines the four
actual folded Weyl generators with the existing `foldedReflection` formulas.

No cardinality-based choice of coordinates, F4 Weyl identification, weighted
sum, or finite-field faithfulness statement is used or asserted.
Source-only draft: not compiled or audited by this sidecar. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.TwistedE6.FixedSpaceAdapter

open Classical RootData FixedWeylFaithfulness Atlas.Comparisons.E6Lattice

local instance adapterRootFintype : Fintype E6Data.Root := Fintype.ofFinite _

/-- Original lattice labels, followed by the existing public base-support indexing. -/
def latticeBaseEquiv : Fin 6 ≃ E6Data.base.support :=
  E6Data.nodeEquiv.trans E6Data.baseIndexEquiv

theorem latticeBaseEquiv_root (i : Fin 6) :
    (latticeBaseEquiv i).val = E6Data.simpleRoot i := by
  change (E6Data.baseIndexEquiv (E6Data.nodeEquiv i)).val = E6Data.simpleRoot i
  rw [E6Data.baseIndexEquiv_apply, Equiv.symm_apply_apply]

theorem latticeBaseEquiv_diagram (i : Fin 6) :
    baseDiagram (latticeBaseEquiv i) = latticeBaseEquiv (latticeNode i) := by
  apply Subtype.ext
  simp only [baseDiagram_root, latticeBaseEquiv_root, rootDiagram_simple]

/-- Reindex the actual rational root-coordinate space into the original six lattice coordinates. -/
def rootSpaceToLattice : RootSpace ≃ₗ[ℚ] (Fin 6 → ℚ) where
  toFun x i := x (latticeBaseEquiv i)
  invFun x j := x (latticeBaseEquiv.symm j)
  left_inv x := by
    funext j
    exact congrArg x (latticeBaseEquiv.apply_symm_apply j)
  right_inv x := by
    funext i
    exact congrArg x (latticeBaseEquiv.symm_apply_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rootSpaceToLattice_diagram (x : RootSpace) :
    rootSpaceToLattice (rootSpaceDiagram x) = latticeDiagram ℚ (rootSpaceToLattice x) := by
  funext i
  change x (baseDiagram (latticeBaseEquiv i)) = x (latticeBaseEquiv (latticeNode i))
  rw [latticeBaseEquiv_diagram]

theorem rootSpaceToLattice_simple (i : Fin 6) :
    rootSpaceToLattice (rootVector (E6Data.simpleRoot i)) = Pi.single i (1 : ℚ) := by
  funext j
  change rationalRootCoordinates E6Data.pairing E6Data.base (E6Data.simpleRoot i)
    (latticeBaseEquiv j) = (Pi.single i (1 : ℚ) : Fin 6 → ℚ) j
  rw [← latticeBaseEquiv_root i, rationalRootCoordinates_simple]
  simp only [Equiv.apply_eq_iff_eq, Pi.single_apply, eq_comm]

/-- The rational basis coordinates of every actual root are its original integral
coordinates, cast to Q, after this precise reindexing. -/
theorem rootSpaceToLattice_root (β : E6Data.Root) :
    rootSpaceToLattice (rootVector β) = fun i => (β.val i : ℚ) := by
  have hsum : E6Data.pairing.root β =
      ∑ i : Fin 6, β.val i • E6Data.pairing.root (E6Data.simpleRoot i) := by
    change β.val = ∑ i : Fin 6, β.val i • Pi.single i (1 : ℤ)
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]
  have hc : rootVector β =
      ∑ i : Fin 6, (β.val i : ℚ) • rootVector (E6Data.simpleRoot i) :=
    rationalRootCoordinates_of_sum E6Data.pairing E6Data.base β
      E6Data.simpleRoot β.val hsum
  calc
    rootSpaceToLattice (rootVector β) =
        rootSpaceToLattice (∑ i : Fin 6, (β.val i : ℚ) • rootVector (E6Data.simpleRoot i)) :=
      congrArg rootSpaceToLattice hc
    _ = ∑ i : Fin 6, (β.val i : ℚ) • Pi.single i (1 : ℚ) := by
      simp only [map_sum, map_smul, rootSpaceToLattice_simple]
    _ = fun i => (β.val i : ℚ) := by
      funext j
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]

/-- Read the two pair coordinates, the central coordinate, and the branch coordinate. -/
def foldedProjection : (Fin 6 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := ![x 0, x 1, x 2, x 5]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' a x := by ext i; fin_cases i <;> rfl

theorem foldedProjection_foldedCoordinates (v : Fin 4 → ℚ) :
    foldedProjection (foldedCoordinates ℚ v) = v := by
  funext i
  fin_cases i <;> rfl

theorem rootSpaceToLattice_fixed (x : fixedRootSpace) :
    latticeDiagram ℚ (rootSpaceToLattice x.val) = rootSpaceToLattice x.val := by
  have hx : rootSpaceDiagram x.val = x.val := x.property
  exact (rootSpaceToLattice_diagram x.val).symm.trans (congrArg rootSpaceToLattice hx)

theorem foldedCoordinates_preimage_mem (v : Fin 4 → ℚ) :
    rootSpaceToLattice.symm (foldedCoordinates ℚ v) ∈ fixedRootSpace := by
  change rootSpaceDiagram (rootSpaceToLattice.symm (foldedCoordinates ℚ v)) =
    rootSpaceToLattice.symm (foldedCoordinates ℚ v)
  apply rootSpaceToLattice.injective
  rw [rootSpaceToLattice_diagram]
  simp only [LinearEquiv.apply_symm_apply]
  exact latticeDiagram_foldedCoordinates ℚ v

/-- Explicit coordinates on the literal audited fixed subspace, with explicit inverse. -/
def fixedRootSpaceCoordinates : fixedRootSpace ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := foldedProjection (rootSpaceToLattice x.val)
  invFun v := ⟨rootSpaceToLattice.symm (foldedCoordinates ℚ v), foldedCoordinates_preimage_mem v⟩
  left_inv x := by
    apply Subtype.ext
    apply rootSpaceToLattice.injective
    change rootSpaceToLattice (rootSpaceToLattice.symm
      (foldedCoordinates ℚ (foldedProjection (rootSpaceToLattice x.val)))) =
        rootSpaceToLattice x.val
    rw [LinearEquiv.apply_symm_apply]
    exact foldedCoordinates_of_fixed ℚ (rootSpaceToLattice x.val) (rootSpaceToLattice_fixed x)
  right_inv v := by
    change foldedProjection (rootSpaceToLattice (rootSpaceToLattice.symm
      (foldedCoordinates ℚ v))) = v
    rw [LinearEquiv.apply_symm_apply]
    exact foldedProjection_foldedCoordinates v
  map_add' x y := by
    change foldedProjection (rootSpaceToLattice (x.val + y.val)) = _
    rw [map_add, map_add]
  map_smul' a x := by
    change foldedProjection (rootSpaceToLattice (a • x.val)) = _
    simp only [map_smul, RingHom.id_apply]

/-- The four output coordinates in the existing public Chevalley node numbering. -/
theorem fixedRootSpaceCoordinates_public (x : fixedRootSpace) :
    fixedRootSpaceCoordinates x =
      ![x.val (E6Data.baseIndexEquiv 0), x.val (E6Data.baseIndexEquiv 2),
        x.val (E6Data.baseIndexEquiv 3), x.val (E6Data.baseIndexEquiv 1)] := rfl

theorem fixedRootSpaceCoordinates_expand (x : fixedRootSpace) :
    foldedCoordinates ℚ (fixedRootSpaceCoordinates x) = rootSpaceToLattice x.val :=
  foldedCoordinates_of_fixed ℚ (rootSpaceToLattice x.val) (rootSpaceToLattice_fixed x)

theorem fixedRootSpaceCoordinates_symm_lattice (v : Fin 4 → ℚ) :
    rootSpaceToLattice (fixedRootSpaceCoordinates.symm v).val = foldedCoordinates ℚ v :=
  rootSpaceToLattice.apply_symm_apply (foldedCoordinates ℚ v)

/-- The inverse has public-node coordinates (a,d,b,c,b,a). -/
theorem fixedRootSpaceCoordinates_symm_public (v : Fin 4 → ℚ) (i : Fin 6) :
    (fixedRootSpaceCoordinates.symm v).val (E6Data.baseIndexEquiv i) =
      ![v 0, v 3, v 1, v 2, v 1, v 0] i := by
  change foldedCoordinates ℚ v
    (E6Data.nodeEquiv.symm (E6Data.baseIndexEquiv.symm (E6Data.baseIndexEquiv i))) = _
  rw [Equiv.symm_apply_apply]
  fin_cases i <;> rfl

/-- Bundle the same six-coordinate folded lifts using the existing linear simple reflections. -/
def foldedLiftLinear (a : Fin 4) : (Fin 6 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ) :=
  match a with
  | 0 => (reflectionLinearEquiv ℚ 0).toLinearMap.comp (reflectionLinearEquiv ℚ 4).toLinearMap
  | 1 => (reflectionLinearEquiv ℚ 1).toLinearMap.comp (reflectionLinearEquiv ℚ 3).toLinearMap
  | 2 => (reflectionLinearEquiv ℚ 2).toLinearMap
  | 3 => (reflectionLinearEquiv ℚ 5).toLinearMap

theorem foldedLiftLinear_apply (a : Fin 4) (x : Fin 6 → ℚ) :
    foldedLiftLinear a x = foldedReflectionLift ℚ a x := by
  fin_cases a <;> rfl

/-- Scalar extension respects the existing literal folded-reflection formulas. -/
theorem foldedReflectionLift_cast (a : Fin 4) (x : Fin 6 → ℤ) :
    (fun j => (foldedReflectionLift ℤ a x j : ℚ)) =
      foldedReflectionLift ℚ a (fun j => (x j : ℚ)) := by
  funext j
  fin_cases a <;> fin_cases j <;> simp [foldedReflectionLift, reflection]

/-- The audited actual Weyl generator acts by the literal lattice lift on every
rational vector. Equality on the actual simple-root basis proves this identity. -/
theorem rootSpaceToLattice_generator (a : Fin 4) (x : RootSpace) :
    rootSpaceToLattice (weylLinear (e6FoldedWeylGenerator a) x) =
      foldedReflectionLift ℚ a (rootSpaceToLattice x) := by
  have h : rootSpaceToLattice.toLinearMap.comp (weylLinear (e6FoldedWeylGenerator a)) =
      (foldedLiftLinear a).comp rootSpaceToLattice.toLinearMap := by
    apply (Pi.basisFun ℚ E6Data.base.support).ext
    intro j
    rw [← rationalRootCoordinates_simple_eq_basis E6Data.pairing E6Data.base j]
    change rootSpaceToLattice (weylLinear (e6FoldedWeylGenerator a) (rootVector j.val)) =
      foldedLiftLinear a (rootSpaceToLattice (rootVector j.val))
    rw [weylLinear_root, rootSpaceToLattice_root, foldedLiftLinear_apply,
      rootSpaceToLattice_root, e6FoldedWeylGenerator_coordinates]
    exact foldedReflectionLift_cast a j.val.val
  have hx := congrArg (fun f : RootSpace →ₗ[ℚ] (Fin 6 → ℚ) => f x) h
  change rootSpaceToLattice (weylLinear (e6FoldedWeylGenerator a) x) = foldedLiftLinear a
    (rootSpaceToLattice x) at hx
  exact hx.trans (foldedLiftLinear_apply a (rootSpaceToLattice x))

/-- Exact intertwining with the existing restriction to the literal fixed subspace. -/
theorem fixedRootSpaceCoordinates_generator (a : Fin 4) (x : fixedRootSpace) :
    fixedRootSpaceCoordinates
        (fixedRootSpaceRestriction (e6FoldedWeylGenerator a) (e6FoldedWeylGenerator_fixed a) x) =
      foldedReflection ℚ a (fixedRootSpaceCoordinates x) := by
  apply foldedCoordinates_injective ℚ
  calc
    _ = rootSpaceToLattice
        (fixedRootSpaceRestriction (e6FoldedWeylGenerator a) (e6FoldedWeylGenerator_fixed a) x).val :=
      fixedRootSpaceCoordinates_expand _
    _ = foldedReflectionLift ℚ a (rootSpaceToLattice x.val) :=
      rootSpaceToLattice_generator a x.val
    _ = foldedReflectionLift ℚ a (foldedCoordinates ℚ (fixedRootSpaceCoordinates x)) := by
      rw [fixedRootSpaceCoordinates_expand]
    _ = foldedCoordinates ℚ (foldedReflection ℚ a (fixedRootSpaceCoordinates x)) :=
      (foldedReflection_intertwines ℚ a (fixedRootSpaceCoordinates x)).symm

/-- Actual restricted folded action transported through the explicit four coordinates. -/
def fourGenerator (a : Fin 4) : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) :=
  fixedRootSpaceCoordinates.toLinearMap.comp
    ((fixedRootSpaceRestriction (e6FoldedWeylGenerator a) (e6FoldedWeylGenerator_fixed a)).comp
      fixedRootSpaceCoordinates.symm.toLinearMap)

theorem fourGenerator_apply (a : Fin 4) (v : Fin 4 → ℚ) :
    fourGenerator a v = foldedReflection ℚ a v := by
  change fixedRootSpaceCoordinates
    (fixedRootSpaceRestriction (e6FoldedWeylGenerator a) (e6FoldedWeylGenerator_fixed a)
      (fixedRootSpaceCoordinates.symm v)) = _
  rw [fixedRootSpaceCoordinates_generator, LinearEquiv.apply_symm_apply]

theorem fourGenerator_zero (v : Fin 4 → ℚ) :
    fourGenerator 0 v = ![v 1 - v 0, v 1, v 2, v 3] := by
  rw [fourGenerator_apply]
  funext j
  fin_cases j <;> simp [foldedReflection]

theorem fourGenerator_one (v : Fin 4 → ℚ) :
    fourGenerator 1 v = ![v 0, v 0 + v 2 - v 1, v 2, v 3] := by
  rw [fourGenerator_apply]
  funext j
  fin_cases j <;> simp [foldedReflection]

theorem fourGenerator_two (v : Fin 4 → ℚ) :
    fourGenerator 2 v = ![v 0, v 1, 2 * v 1 + v 3 - v 2, v 3] := by
  rw [fourGenerator_apply]
  funext j
  fin_cases j <;> simp [foldedReflection]

theorem fourGenerator_three (v : Fin 4 → ℚ) :
    fourGenerator 3 v = ![v 0, v 1, v 2, v 2 - v 3] := by
  rw [fourGenerator_apply]
  funext j
  fin_cases j <;> simp [foldedReflection]

end Atlas.Chevalley.TwistedE6.FixedSpaceAdapter
