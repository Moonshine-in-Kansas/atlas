import Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.Commutator.Basic

/-!
Source-only restriction of the binary action faithfulness candidate to an
arbitrary actual subgroup and, in particular, the literal commutator subgroup.
No derived order, index, transitivity, perfectness, simplicity, or Tits comparison
is used or asserted. The earlier BinaryDerivedAction draft is not imported.
No Lean, Lake, checker, audit, or resource measurement was run for this draft.
-/

noncomputable section
namespace Atlas.ReeF4

theorem binarySubgroup_specialPoints_faithful (H : Subgroup (Model (ZMod 2) 0)) :
    FaithfulSMul H (SpecialPoints (F := ZMod 2) 0) :=
  inferInstance

/-- The carrier is literally the commutator of the independent binary Ree model. -/
theorem binaryDerived_specialPoints_faithful :
    FaithfulSMul ↥(commutator (Model (ZMod 2) 0)) (SpecialPoints (F := ZMod 2) 0) :=
  binarySubgroup_specialPoints_faithful _

/-- The inherited derived action is exactly restriction of the full action. -/
theorem binaryDerived_specialPoints_toPermHom_eq_restrict :
    MulAction.toPermHom ↥(commutator (Model (ZMod 2) 0))
        (SpecialPoints (F := ZMod 2) 0) =
      (MulAction.toPermHom (Model (ZMod 2) 0) (SpecialPoints (F := ZMod 2) 0)).comp
        (commutator (Model (ZMod 2) 0)).subtype := by
  apply MonoidHom.ext
  intro g
  apply Equiv.ext
  intro p
  rfl

theorem binaryDerived_specialPoints_toPermHom_injective :
    Function.Injective
      (MulAction.toPermHom ↥(commutator (Model (ZMod 2) 0))
        (SpecialPoints (F := ZMod 2) 0)) :=
  MulAction.toPerm_injective

theorem binaryDerived_specialPoints_toPermHom_ker_eq_bot :
    (MulAction.toPermHom ↥(commutator (Model (ZMod 2) 0))
      (SpecialPoints (F := ZMod 2) 0)).ker = ⊥ :=
  MonoidHom.ker_eq_bot _ binaryDerived_specialPoints_toPermHom_injective

end Atlas.ReeF4
