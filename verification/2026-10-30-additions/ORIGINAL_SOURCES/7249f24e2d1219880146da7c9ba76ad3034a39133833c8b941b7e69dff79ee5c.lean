import FamilyWork.F4ActionAdapter
import FamilyWork.FixedBruhat
import Mathlib.Algebra.Group.Submonoid.Operations

/-! Source-only structural identification of the actual diagram-fixed E6 Weyl
subgroup with the existing actual F4 root-permutation Weyl image.

Both groups act faithfully on the same rational four-space. Their four marked
generators have equal actions, and the existing generation results give equal
linear images. The multiplicative equivalence is induced by those images.
No order recognition, Coxeter presentation, Weyl enumeration, or Poincare
evaluation is used. E6 word weights remain 2,2,1,1. Uncompiled and unaudited. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.TwistedE6.FoldedWeylIdentification

open Classical RootData FixedWeylFaithfulness FixedSpaceAdapter F4ActionAdapter

local instance identificationRootFintype : Fintype E6Data.Root := Fintype.ofFinite _

/-- The actual centralizer of the diagram inside the actual E6 Weyl image.
The commutation orientation matches the existing FixedBruhat index exactly. -/
def diagramFixedWeylSubgroup : Subgroup E6RootWeyl where
  carrier := {w | Commute w.val rootDiagram}
  one_mem' := Commute.one_left rootDiagram
  mul_mem' := fun hw hv => hw.mul_left hv
  inv_mem' := fun hw => hw.inv_left

theorem mem_diagramFixedWeylSubgroup_iff (w : E6RootWeyl) :
    w ∈ diagramFixedWeylSubgroup ↔ Function.Commute rootDiagram w.val := by
  constructor
  · intro hw β
    have hc : Commute w.val rootDiagram := hw
    exact (congrArg (fun p : Equiv.Perm E6Data.Root => p β) hc.eq).symm
  · intro hw
    change w.val * rootDiagram = rootDiagram * w.val
    apply Equiv.ext
    intro β
    exact (hw β).symm

theorem fixed_commute (w : diagramFixedWeylSubgroup) :
    Function.Commute rootDiagram w.val.val :=
  (mem_diagramFixedWeylSubgroup_iff w.val).mp w.property

/-- Bundle the inherited literal fixed-space restrictions multiplicatively. -/
def fixedRestrictionAction :
    diagramFixedWeylSubgroup →* Module.End ℚ fixedRootSpace where
  toFun w := fixedRootSpaceRestriction w.val (fixed_commute w)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change weylLinear 1 x.val = x.val
    exact congrArg (fun T : Module.End ℚ RootSpace => T x.val) weylLinear_one
  map_mul' w v := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change weylLinear (w.val * v.val) x.val =
      weylLinear w.val (weylLinear v.val x.val)
    exact congrArg (fun T : Module.End ℚ RootSpace => T x.val)
      ((rationalActionHom E6Data.pairing E6Data.base).map_mul w.val v.val)

/-- The previously proved fixed-space kernel theorem gives full injectivity. -/
theorem fixedRestrictionAction_injective : Function.Injective fixedRestrictionAction := by
  have hker : ∀ z : diagramFixedWeylSubgroup, fixedRestrictionAction z = 1 → z = 1 := by
    intro z hz
    apply Subtype.ext
    apply eq_one_of_fixedRootSpace_pointwise z.val (fixed_commute z)
    intro x
    exact congrArg Subtype.val
      (congrArg (fun T : Module.End ℚ fixedRootSpace => T x) hz)
  intro w v h
  have hz : fixedRestrictionAction (w⁻¹ * v) = 1 := by
    rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]
  exact inv_mul_eq_one.mp (hker (w⁻¹ * v) hz)

/-- The actual faithful E6 fixed-space action in the audited explicit coordinates. -/
def fixedAction : diagramFixedWeylSubgroup →* Module.End ℚ FourSpace :=
  fixedRootSpaceCoordinates.conjRingEquiv.toMonoidHom.comp fixedRestrictionAction

theorem fixedAction_apply (w : diagramFixedWeylSubgroup) (v : FourSpace) :
    fixedAction w v = fixedRootSpaceCoordinates
      (fixedRootSpaceRestriction w.val (fixed_commute w) (fixedRootSpaceCoordinates.symm v)) := rfl

theorem fixedAction_injective : Function.Injective fixedAction := by
  intro w v h
  apply fixedRestrictionAction_injective
  apply fixedRootSpaceCoordinates.conjRingEquiv.injective
  exact h

def fixedGenerator (a : Fin 4) : diagramFixedWeylSubgroup :=
  ⟨e6FoldedWeylGenerator a,
    (mem_diagramFixedWeylSubgroup_iff _).mpr (e6FoldedWeylGenerator_fixed a)⟩

theorem fixedAction_generator (a : Fin 4) :
    fixedAction (fixedGenerator a) = fourGenerator a := by
  ext v
  rfl

def fixedWord (l : List (Fin 4)) : diagramFixedWeylSubgroup :=
  ⟨e6FoldedWeylWord l,
    (mem_diagramFixedWeylSubgroup_iff _).mpr (e6FoldedWeylWord_fixed l)⟩

@[simp] theorem fixedWord_nil : fixedWord [] = 1 := rfl

theorem fixedWord_cons (a : Fin 4) (l : List (Fin 4)) :
    fixedWord (a :: l) = fixedGenerator a * fixedWord l := by
  apply Subtype.ext
  exact e6FoldedWeylWord_cons a l

/-- All actual commuting Weyl elements occur, with the inherited exact E6 weight. -/
theorem exists_fixedWord (w : diagramFixedWeylSubgroup) :
    ∃ l : List (Fin 4), fixedWord l = w ∧
      e6FoldedWeylWordWeight l = rootWeylLength E6Data.pairing E6Data.base w.val := by
  obtain ⟨l, hl, hweight⟩ := e6RootWeyl_exists_foldedWord w.val (fixed_commute w)
  exact ⟨l, Subtype.ext hl, hweight⟩

/-- The same letters evaluated in the existing F4 base indexing. -/
def f4Word (l : List (Fin 4)) : F4Weyl :=
  rootWeylWord F4Data.pairing F4Data.base (l.map F4Data.baseIndexEquiv)

@[simp] theorem f4Word_nil : f4Word [] = 1 := rfl

theorem f4Word_cons (a : Fin 4) (l : List (Fin 4)) :
    f4Word (a :: l) = f4Simple a * f4Word l := by
  simp only [f4Word, rootWeylWord, f4Simple, List.map_cons, List.prod_cons]

theorem exists_f4Word (w : F4Weyl) : ∃ l : List (Fin 4), f4Word l = w := by
  obtain ⟨l, _hlen, hl⟩ := rootWeylLength_spec F4Data.pairing F4Data.base w
  have he : rootWeylWord F4Data.pairing F4Data.base l = w := by
    apply Subtype.ext
    exact (rootWeylWord_val F4Data.pairing F4Data.base l).trans hl
  refine ⟨l.map F4Data.baseIndexEquiv.symm, ?_⟩
  simpa [f4Word, List.map_map] using he

/-- All word actions agree because the four actual generator actions agree. -/
theorem word_actions_equal (l : List (Fin 4)) :
    fixedAction (fixedWord l) = f4Action (f4Word l) := by
  induction l with
  | nil => rw [fixedWord_nil, f4Word_nil, map_one, map_one]
  | cons a l ih =>
    rw [fixedWord_cons, f4Word_cons, map_mul, map_mul, ih,
      fixedAction_generator, f4Action_simple]

/-- Actual word relations coincide; both implications use faithful linear actions. -/
theorem word_eq_iff (l r : List (Fin 4)) :
    fixedWord l = fixedWord r ↔ f4Word l = f4Word r := by
  constructor
  · intro h
    apply f4Action_injective
    rw [← word_actions_equal, ← word_actions_equal, h]
  · intro h
    apply fixedAction_injective
    rw [word_actions_equal, word_actions_equal, h]

/-- Equality of concrete rational linear images, derived from generation. -/
theorem action_images_equal : MonoidHom.mrange fixedAction = MonoidHom.mrange f4Action := by
  ext T
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨l, hl, _hweight⟩ := exists_fixedWord w
    refine ⟨f4Word l, ?_⟩
    rw [← word_actions_equal, hl]
  · rintro ⟨w, rfl⟩
    obtain ⟨l, hl⟩ := exists_f4Word w
    refine ⟨fixedWord l, ?_⟩
    rw [word_actions_equal, hl]

private def faithfulImageEquiv {G : Type*} [Group G]
    (f : G →* Module.End ℚ FourSpace) (hf : Function.Injective f) : G ≃* MonoidHom.mrange f :=
  MulEquiv.ofBijective f.mrangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.mrangeRestrict_surjective⟩

private def commonImageEquiv : MonoidHom.mrange fixedAction ≃* MonoidHom.mrange f4Action where
  toFun x := ⟨x.val, by rw [← action_images_equal]; exact x.property⟩
  invFun x := ⟨x.val, by rw [action_images_equal]; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Genuine multiplicative identification, induced by the common faithful image. -/
def fixedWeylEquivF4 : diagramFixedWeylSubgroup ≃* F4Weyl :=
  (faithfulImageEquiv fixedAction fixedAction_injective).trans
    (commonImageEquiv.trans (faithfulImageEquiv f4Action f4Action_injective).symm)

/-- The equivalence preserves the actual rational action, not only the abstract group. -/
theorem fixedWeylEquivF4_action (w : diagramFixedWeylSubgroup) :
    f4Action (fixedWeylEquivF4 w) = fixedAction w := by
  have he := (faithfulImageEquiv f4Action f4Action_injective).apply_symm_apply
    (commonImageEquiv (faithfulImageEquiv fixedAction fixedAction_injective w))
  exact congrArg Subtype.val he

theorem fixedWeylEquivF4_generator (a : Fin 4) :
    fixedWeylEquivF4 (fixedGenerator a) = f4Simple a := by
  apply f4Action_injective
  rw [fixedWeylEquivF4_action, fixedAction_generator, f4Action_simple]

theorem fixedWeylEquivF4_word (l : List (Fin 4)) :
    fixedWeylEquivF4 (fixedWord l) = f4Word l := by
  apply f4Action_injective
  rw [fixedWeylEquivF4_action, word_actions_equal]

/-- Explicit linear comparison with the actual F4 base-support root space. -/
def fixedSpaceToF4 : fixedRootSpace ≃ₗ[ℚ] (F4Data.base.support → ℚ) :=
  fixedRootSpaceCoordinates.trans f4Coordinates.symm

/-- The multiplicative comparison intertwines every actual fixed Weyl element. -/
theorem fixedSpaceToF4_intertwines (w : diagramFixedWeylSubgroup) (x : fixedRootSpace) :
    fixedSpaceToF4 (fixedRootSpaceRestriction w.val (fixed_commute w) x) =
      rationalRootWeylLinear F4Data.pairing F4Data.base (fixedWeylEquivF4 w)
        (fixedSpaceToF4 x) := by
  apply f4Coordinates.injective
  change f4Coordinates (f4Coordinates.symm (fixedRootSpaceCoordinates
      (fixedRootSpaceRestriction w.val (fixed_commute w) x))) =
    f4Coordinates (rationalRootWeylLinear F4Data.pairing F4Data.base (fixedWeylEquivF4 w)
      (f4Coordinates.symm (fixedRootSpaceCoordinates x)))
  rw [LinearEquiv.apply_symm_apply]
  have he := congrArg (fun T : Module.End ℚ FourSpace => T (fixedRootSpaceCoordinates x))
    (fixedWeylEquivF4_action w)
  rw [f4Action_apply, fixedAction_apply, LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- Literal identification with the existing Bruhat label subtype. No carrier is changed. -/
def fixedBruhatIndexEquiv : E6DiagramFixedWeyl ≃ diagramFixedWeylSubgroup where
  toFun w := ⟨w.val, w.property⟩
  invFun w := ⟨w.val, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Set equivalence on the exact index type already used in the fixed Bruhat theorem. -/
def fixedBruhatIndexEquivF4 : E6DiagramFixedWeyl ≃ F4Weyl :=
  fixedBruhatIndexEquiv.trans fixedWeylEquivF4.toEquiv

/-- The E6 exponent transported to F4. This is deliberately not the ordinary F4 length. -/
def inheritedE6Length (w : F4Weyl) : ℕ :=
  rootWeylLength E6Data.pairing E6Data.base (fixedWeylEquivF4.symm w).val

/-- The inherited weight-exact E6 word becomes a word in the same four F4 nodes.
Its weight is the existing sum of letters 2,2,1,1, without any Poincare claim. -/
theorem exists_f4Word_exact_inheritedE6Length (w : F4Weyl) :
    ∃ l : List (Fin 4), f4Word l = w ∧
      e6FoldedWeylWordWeight l = inheritedE6Length w := by
  obtain ⟨l, hl, hweight⟩ := exists_fixedWord (fixedWeylEquivF4.symm w)
  refine ⟨l, ?_, hweight⟩
  calc
    f4Word l = fixedWeylEquivF4 (fixedWord l) := (fixedWeylEquivF4_word l).symm
    _ = fixedWeylEquivF4 (fixedWeylEquivF4.symm w) := congrArg fixedWeylEquivF4 hl
    _ = w := fixedWeylEquivF4.apply_symm_apply w

end Atlas.Chevalley.TwistedE6.FoldedWeylIdentification
