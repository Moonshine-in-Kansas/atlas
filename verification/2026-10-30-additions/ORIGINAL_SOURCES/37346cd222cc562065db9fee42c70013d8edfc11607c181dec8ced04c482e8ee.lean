import F4Work.SpecialRootRigidity
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.FieldTheory.Finite.Basic

/-!
Source-only draft for the actual SpecialPoints action of Model (ZMod 2) 0.
The unique binary unit removes the scalar ambiguity in a fixed projective point.
The endpoint uses six explicitly special roots and actual cross-product rigidity.
No BinaryDerivedAction, Ree order, generation, or point-count module is imported.
No Lean, Lake, checker, audit, or resource measurement was run for this draft.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

/-- The scalar ambiguity in projective representatives is trivial over F₂. -/
theorem binary_specialPoints_unit_eq_one (a : (ZMod 2)ˣ) : a = 1 := by
  have h : a ^ 1 = 1 := ZMod.units_pow_card_sub_one_eq_one 2 a
  simpa only [pow_one] using h

/-- Fixing a special projective point fixes its actual binary representative. -/
theorem binaryModel_fixes_vector_of_fixes_specialPoint
    (g : Model (ZMod 2) 0) {u : TraceZero (ZMod 2)} (hu : IsSpecialVector 0 u)
    (hp : g • specialPointMk 0 u hu = specialPointMk 0 u hu) : g.val u = u := by
  have he : specialPointMk 0 (g.val u) (hu.map_model g) = specialPointMk 0 u hu :=
    (specialPointMk_smul 0 g u hu).symm.trans hp
  obtain ⟨a, ha⟩ :=
    (specialPointMk_eq_iff 0 (g.val u) u (hu.map_model g) hu).mp he
  rw [binary_specialPoints_unit_eq_one a, one_smul] at ha
  exact ha.symm

/-- The kernel of the actual binary projective special-point action is trivial.
No statement about its order, transitivity, or generated subgroup is a premise. -/
theorem binaryModel_eq_one_of_fix_specialPoints (g : Model (ZMod 2) 0)
    (hfix : ∀ p : SpecialPoints (F := ZMod 2) 0, g • p = p) : g = 1 := by
  have fix (u : TraceZero (ZMod 2)) (hu : IsSpecialVector 0 u) : g.val u = u :=
    binaryModel_fixes_vector_of_fixes_specialPoint g hu (hfix (specialPointMk 0 u hu))
  exact model_eq_one_of_fix_six_special_roots g
    (fix (rootVector (0,7)) (isSpecialVector_oppositeRoot 0))
    (fix (rootVector (0,0)) (isSpecialVector_firstRoot 0))
    (fix (rootVector (2,0)) (isSpecialVector_root_two_zero 0))
    (fix (rootVector (0,2)) (isSpecialVector_root_zero_two 0))
    (fix (rootVector (0,5)) (isSpecialVector_root_zero_five 0))
    (fix (rootVector (2,1)) (isSpecialVector_root_two_one 0))

/-- Faithfulness for the existing action; no replacement action is defined. -/
theorem binarySpecialPoints_faithfulSMul :
    FaithfulSMul (Model (ZMod 2) 0) (SpecialPoints (F := ZMod 2) 0) :=
  faithfulSMul_iff.mpr binaryModel_eq_one_of_fix_specialPoints

attribute [instance] binarySpecialPoints_faithfulSMul

theorem binarySpecialPoints_toPermHom_injective :
    Function.Injective
      (MulAction.toPermHom (Model (ZMod 2) 0) (SpecialPoints (F := ZMod 2) 0)) :=
  MulAction.toPerm_injective

theorem binarySpecialPoints_toPermHom_ker_eq_bot :
    (MulAction.toPermHom (Model (ZMod 2) 0) (SpecialPoints (F := ZMod 2) 0)).ker = ⊥ :=
  MonoidHom.ker_eq_bot _ binarySpecialPoints_toPermHom_injective

end Atlas.ReeF4
