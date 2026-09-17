import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Symplectic.BinarySignKernel
import Atlas.Families.Alternating.Basic

/-! # The actual binary B₂ group and its alternating derived subgroup

The six-point action is the already constructed action on odd quadratic
refinements. The full B₂(2) model remains S₆ of order 720; only its actual
commutator subgroup is the simple group A₆ of order 360.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Symplectic.BinaryException

/-- The genuine odd-refinement action identifies the actual binary B₂ quotient with S₆. -/
def b2BinaryEquivSymmetric :
    ProjectiveElementary (formB 2 (ZMod 2)) ≃* Equiv.Perm (Fin 6) :=
  (evenProjectiveBEquivPSp (F := ZMod 2) (by decide : 0 < 2)).trans
    (projectionEquiv.symm.trans (permutationEquiv.trans sixFormsEquiv.symm.permCongrHom))

/-- The actual derived subgroup maps exactly onto the existing alternating subgroup. -/
theorem b2Binary_commutator_map :
    (commutator (ProjectiveElementary (formB 2 (ZMod 2)))).map
      b2BinaryEquivSymmetric.toMonoidHom = alternatingGroup (Fin 6) := by
  rw [map_commutator_eq, b2BinaryEquivSymmetric.toMonoidHom.range_eq_top.mpr
    b2BinaryEquivSymmetric.surjective]
  exact alternatingGroup.commutator_perm_eq (by simp)

/-- Restriction of the actual six-point action to the actual derived subgroup. -/
def b2BinaryDerivedEquivAlternating :
    commutator (ProjectiveElementary (formB 2 (ZMod 2))) ≃*
      Atlas.Families.Alternating.Model 6 :=
  ((commutator _).equivMapOfInjective b2BinaryEquivSymmetric.toMonoidHom
    b2BinaryEquivSymmetric.injective).trans (MulEquiv.subgroupCongr b2Binary_commutator_map)

theorem card_b2Binary : Nat.card (ProjectiveElementary (formB 2 (ZMod 2))) = 720 := by
  rw [Nat.card_congr b2BinaryEquivSymmetric.toEquiv, Nat.card_perm, Nat.card_fin]
  decide

theorem b2Binary_not_simple : ¬ IsSimpleGroup (ProjectiveElementary (formB 2 (ZMod 2))) := by
  intro hs
  letI := hs
  haveI := (evenProjectiveBEquivPSp (F := ZMod 2) (by decide : 0 < 2)).symm.isSimpleGroup
  exact psp_binary_four_not_simple inferInstance

theorem card_b2BinaryDerived :
    Nat.card (commutator (ProjectiveElementary (formB 2 (ZMod 2)))) = 360 := by
  rw [Nat.card_congr b2BinaryDerivedEquivAlternating.toEquiv,
    Atlas.Families.Alternating.card_factorial 6 (by decide)]
  decide

theorem b2BinaryDerived_simple :
    IsSimpleGroup (commutator (ProjectiveElementary (formB 2 (ZMod 2)))) := by
  letI := Atlas.Families.Alternating.isSimpleGroup 6 (by change 5 ≤ 6; decide)
  exact b2BinaryDerivedEquivAlternating.isSimpleGroup

theorem b2BinaryDerived_noncommutative :
    ∃ a b : commutator (ProjectiveElementary (formB 2 (ZMod 2))), a * b ≠ b * a := by
  obtain ⟨a,b,h⟩ := Atlas.Families.Alternating.exists_mul_ne_mul 6 (by decide)
  refine ⟨b2BinaryDerivedEquivAlternating.symm a, b2BinaryDerivedEquivAlternating.symm b, ?_⟩
  intro hc
  apply h
  simpa using congrArg b2BinaryDerivedEquivAlternating hc

end Atlas.Orthogonal
