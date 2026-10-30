import Atlas.LinearGroups.Chevalley.TwistedE6.InvariantSimpleDescent
import Atlas.LinearGroups.Chevalley.RootData.RationalRootWeylLinear
import Atlas.LinearGroups.Chevalley.RootData.RationalRootPairPositiveLevi

/-! Faithfulness on the diagram-fixed rational E6 root space.

The Weyl element belongs to the inherited actual root-permutation image.
The linear map is the existing `rationalRootWeylLinear`, and the diagram
operator below is verified on every actual root. A commuting Weyl element
preserves the fixed subspace, so its literal linear restriction is defined.

A nonidentity commuting element has a whole descending simple orbit.
The corresponding two-term symmetrization is fixed by the diagram and has
height two, whereas its image has negative height. At a fixed simple node
the symmetrization is twice the simple root; no division is used.

No folded generation, F4 identification, normalizer quotient, or finite-field
linear-faithfulness statement is asserted. Exact staged verification receipts
are recorded separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.TwistedE6.FixedWeylFaithfulness

open Classical RootData

local instance rootFintype : Fintype E6Data.Root := Fintype.ofFinite _

abbrev RootSpace := E6Data.base.support → ℚ

abbrev rootVector (β : E6Data.Root) : RootSpace :=
  rationalRootCoordinates E6Data.pairing E6Data.base β

abbrev weylLinear (w : E6RootWeyl) : RootSpace →ₗ[ℚ] RootSpace :=
  rationalRootWeylLinear E6Data.pairing E6Data.base w

theorem weylLinear_root (w : E6RootWeyl) (β : E6Data.Root) :
    weylLinear w (rootVector β) = rootVector (w.val β) :=
  rationalRootWeylLinear_root E6Data.pairing E6Data.base w β

/-- The actual diagram in rational simple-root coordinates, indexed by the base. -/
def rootSpaceDiagram : RootSpace ≃ₗ[ℚ] RootSpace where
  toFun x j := x (baseDiagram j)
  invFun x j := x (baseDiagram j)
  left_inv x := by
    funext j
    exact congrArg x (baseDiagram_involutive j)
  right_inv x := by
    funext j
    exact congrArg x (baseDiagram_involutive j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rootSpaceDiagram_simple (j : E6Data.base.support) :
    rootSpaceDiagram (rootVector j.val) = rootVector (baseDiagram j).val := by
  funext k
  change rationalRootCoordinates E6Data.pairing E6Data.base j.val (baseDiagram k) =
    rationalRootCoordinates E6Data.pairing E6Data.base (baseDiagram j).val k
  rw [rationalRootCoordinates_simple, rationalRootCoordinates_simple]
  have he : j = baseDiagram k ↔ baseDiagram j = k := by
    constructor
    · intro h
      rw [h, baseDiagram_involutive]
    · intro h
      rw [← h, baseDiagram_involutive]
  simp only [he]

/-- This coordinate permutation is the diagram action on every actual root. -/
theorem rootSpaceDiagram_root (β : E6Data.Root) :
    rootSpaceDiagram (rootVector β) = rootVector (rootDiagram β) := by
  have hr : E6Data.pairing.root β =
      ∑ j : E6Data.base.support,
        rootSimpleCoefficients E6Data.pairing E6Data.base β j •
          E6Data.pairing.root j.val := by
    have h := congrArg Subtype.val
      (rootSimpleCoefficients_sum E6Data.pairing E6Data.base β)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm
  have hdr : E6Data.pairing.root (rootDiagram β) =
      ∑ j : E6Data.base.support,
        rootSimpleCoefficients E6Data.pairing E6Data.base β j •
          E6Data.pairing.root (rootDiagram j.val) := by
    change latticeDiagram ℤ β.val =
      ∑ j : E6Data.base.support,
        rootSimpleCoefficients E6Data.pairing E6Data.base β j •
          latticeDiagram ℤ j.val.val
    change β.val = ∑ j : E6Data.base.support,
      rootSimpleCoefficients E6Data.pairing E6Data.base β j • j.val.val at hr
    simpa only [map_sum, map_smul] using congrArg (latticeDiagram ℤ) hr
  have hc := rationalRootCoordinates_of_sum E6Data.pairing E6Data.base β
    (fun j : E6Data.base.support => j.val)
    (rootSimpleCoefficients E6Data.pairing E6Data.base β) hr
  have hdc := rationalRootCoordinates_of_sum E6Data.pairing E6Data.base (rootDiagram β)
    (fun j : E6Data.base.support => rootDiagram j.val)
    (rootSimpleCoefficients E6Data.pairing E6Data.base β) hdr
  calc
    rootSpaceDiagram (rootVector β) =
        rootSpaceDiagram (∑ j : E6Data.base.support,
          (rootSimpleCoefficients E6Data.pairing E6Data.base β j : ℚ) •
            rootVector j.val) := congrArg rootSpaceDiagram hc
    _ = ∑ j : E6Data.base.support,
          (rootSimpleCoefficients E6Data.pairing E6Data.base β j : ℚ) •
            rootVector (rootDiagram j.val) := by
      simp only [map_sum, map_smul, rootSpaceDiagram_simple, baseDiagram_root]
    _ = rootVector (rootDiagram β) := hdc.symm

/-- The literal fixed subspace of the actual rational diagram operator. -/
def fixedRootSpace : Submodule ℚ RootSpace where
  carrier := {x | rootSpaceDiagram x = x}
  zero_mem' := map_zero rootSpaceDiagram
  add_mem' := by
    intro x y hx hy
    change rootSpaceDiagram (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    change rootSpaceDiagram (a • x) = a • x
    rw [map_smul, hx]

@[simp] theorem mem_fixedRootSpace (x : RootSpace) :
    x ∈ fixedRootSpace ↔ rootSpaceDiagram x = x := Iff.rfl

/-- Root-permutation commutation extends to the actual rational linear maps. -/
theorem rootSpaceDiagram_commute_weylLinear (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) :
    Function.Commute rootSpaceDiagram (weylLinear w) := by
  have h : rootSpaceDiagram.toLinearMap.comp (weylLinear w) =
      (weylLinear w).comp rootSpaceDiagram.toLinearMap := by
    apply (Pi.basisFun ℚ E6Data.base.support).ext
    intro j
    rw [← rationalRootCoordinates_simple_eq_basis E6Data.pairing E6Data.base j]
    change rootSpaceDiagram (weylLinear w (rootVector j.val)) =
      weylLinear w (rootSpaceDiagram (rootVector j.val))
    rw [weylLinear_root, rootSpaceDiagram_root, rootSpaceDiagram_root, weylLinear_root]
    exact congrArg rootVector (hw j.val)
  intro x
  exact congrArg (fun f : RootSpace →ₗ[ℚ] RootSpace => f x) h

theorem weylLinear_mem_fixedRootSpace (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) (x : RootSpace)
    (hx : x ∈ fixedRootSpace) : weylLinear w x ∈ fixedRootSpace := by
  change rootSpaceDiagram (weylLinear w x) = weylLinear w x
  change rootSpaceDiagram x = x at hx
  rw [rootSpaceDiagram_commute_weylLinear w hw x, hx]

/-- Literal restriction of the existing rational Weyl action to the fixed space. -/
def fixedRootSpaceRestriction (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) : fixedRootSpace →ₗ[ℚ] fixedRootSpace where
  toFun x := ⟨weylLinear w x.val, weylLinear_mem_fixedRootSpace w hw x.val x.property⟩
  map_add' x y := Subtype.ext (map_add (weylLinear w) x.val y.val)
  map_smul' a x := Subtype.ext (map_smul (weylLinear w) a x.val)

@[simp] theorem fixedRootSpaceRestriction_val (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) (x : fixedRootSpace) :
    (fixedRootSpaceRestriction w hw x).val = weylLinear w x.val := rfl

/-- A two-term orbit symmetrization. A fixed node contributes twice its root. -/
def simpleOrbitSum (i : Fin 6) : RootSpace :=
  rootVector (E6Data.baseIndexEquiv i).val +
    rootVector (E6Data.baseIndexEquiv (simpleNode i)).val

theorem simpleOrbitSum_mem (i : Fin 6) : simpleOrbitSum i ∈ fixedRootSpace := by
  change rootSpaceDiagram (simpleOrbitSum i) = simpleOrbitSum i
  simp only [simpleOrbitSum, map_add, rootSpaceDiagram_root,
    e6_rootDiagram_baseIndex, simpleNode_involutive i]
  exact add_comm _ _

abbrev heightFunctional : RootSpace →ₗ[ℚ] ℚ :=
  (Pi.basisFun ℚ E6Data.base.support).sumCoords

theorem height_rootVector (β : E6Data.Root) :
    heightFunctional (rootVector β) = (E6Data.base.height β : ℚ) :=
  rationalRootCoordinates_sumCoords E6Data.pairing E6Data.base β

theorem height_simpleOrbitSum (i : Fin 6) : heightFunctional (simpleOrbitSum i) = 2 := by
  rw [simpleOrbitSum, map_add, height_rootVector, height_rootVector,
    E6Data.base.height_one_of_mem_support (E6Data.baseIndexEquiv i).property,
    E6Data.base.height_one_of_mem_support (E6Data.baseIndexEquiv (simpleNode i)).property] <;>
    norm_num

/-- Precise orbit-sum kernel criterion, independent of a folded-group presentation. -/
theorem eq_one_of_simpleOrbitSums_fixed (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val)
    (hfix : ∀ i : Fin 6, weylLinear w (simpleOrbitSum i) = simpleOrbitSum i) : w = 1 := by
  by_contra hne
  obtain ⟨i, hi, hdi⟩ := e6RootWeyl_exists_simpleDescent_orbit w hw hne
  have hiZ : E6Data.base.height (w.val (E6Data.baseIndexEquiv i).val) < 0 :=
    lt_of_not_ge (fun h => hi (E6Data.base.isPos_iff'.mpr h))
  have hdiZ : E6Data.base.height
      (w.val (E6Data.baseIndexEquiv (simpleNode i)).val) < 0 :=
    lt_of_not_ge (fun h => hdi (E6Data.base.isPos_iff'.mpr h))
  have hiQ : (E6Data.base.height (w.val (E6Data.baseIndexEquiv i).val) : ℚ) < 0 := by
    exact_mod_cast hiZ
  have hdiQ :
      (E6Data.base.height (w.val (E6Data.baseIndexEquiv (simpleNode i)).val) : ℚ) < 0 := by
    exact_mod_cast hdiZ
  have he := congrArg heightFunctional (hfix i)
  rw [height_simpleOrbitSum] at he
  have he' :
      (E6Data.base.height (w.val (E6Data.baseIndexEquiv i).val) : ℚ) +
        (E6Data.base.height (w.val (E6Data.baseIndexEquiv (simpleNode i)).val) : ℚ) = 2 := by
    simpa only [simpleOrbitSum, map_add, weylLinear_root, height_rootVector] using he
  linarith

/-- Faithfulness statement for the actual rational action on the entire fixed space. -/
theorem eq_one_of_fixedRootSpace_pointwise (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val)
    (hfix : ∀ x : fixedRootSpace, weylLinear w x.val = x.val) : w = 1 := by
  apply eq_one_of_simpleOrbitSums_fixed w hw
  intro i
  exact hfix ⟨simpleOrbitSum i, simpleOrbitSum_mem i⟩

theorem weylLinear_one : weylLinear (1 : E6RootWeyl) = LinearMap.id := by
  apply (Pi.basisFun ℚ E6Data.base.support).ext
  intro j
  rw [← rationalRootCoordinates_simple_eq_basis E6Data.pairing E6Data.base j]
  change weylLinear (1 : E6RootWeyl) (rootVector j.val) = rootVector j.val
  exact weylLinear_root (1 : E6RootWeyl) j.val

/-- The actual restriction has trivial identity fiber, with commutation explicit. -/
theorem fixedRootSpaceRestriction_eq_id_iff (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val) :
    fixedRootSpaceRestriction w hw = LinearMap.id ↔ w = 1 := by
  constructor
  · intro h
    apply eq_one_of_fixedRootSpace_pointwise w hw
    intro x
    exact congrArg Subtype.val
      (congrArg (fun f : fixedRootSpace →ₗ[ℚ] fixedRootSpace => f x) h)
  · rintro rfl
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change weylLinear (1 : E6RootWeyl) x.val = x.val
    exact congrArg (fun f : RootSpace →ₗ[ℚ] RootSpace => f x.val) weylLinear_one

/-- Same pointwise conclusion phrased directly with the inherited linear equivalence. -/
theorem eq_one_of_rationalRootWeylEquiv_fixed (w : E6RootWeyl)
    (hw : Function.Commute rootDiagram w.val)
    (hfix : ∀ x : fixedRootSpace,
      rationalRootWeylEquiv E6Data.pairing E6Data.base w x.val = x.val) : w = 1 := by
  apply eq_one_of_fixedRootSpace_pointwise w hw
  intro x
  exact hfix x

end Atlas.Chevalley.TwistedE6.FixedWeylFaithfulness
