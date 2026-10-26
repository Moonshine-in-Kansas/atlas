import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramRoots
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Quotient

/-! The diagram on the actual coroot-dual weight lattice. Its action on the
existing weight/root quotient is inversion. This is a lattice statement;
lifting it to the center of the fixed group remains a separate obligation. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open E6Data Integral.Minuscule

def coordinateDiagram : (Fin 6 → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun v i := v (simpleNode i)
  invFun v i := v (simpleNode i)
  left_inv v := funext fun i => congrArg v (simpleNode_involutive i)
  right_inv v := funext fun i => congrArg v (simpleNode_involutive i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateDiagram_apply (v : Fin 6 → ℤ) (i : Fin 6) :
    coordinateDiagram v i = v (simpleNode i) := rfl

def weightDiagram : WeightLattice pairing ≃ₗ[ℤ] WeightLattice pairing :=
  (indexedWeightCoordinates pairing base baseIndexEquiv).trans
    (coordinateDiagram.trans (indexedWeightCoordinates pairing base baseIndexEquiv).symm)

@[simp] theorem weightDiagram_coordinates (μ : WeightLattice pairing) :
    indexedWeightCoordinates pairing base baseIndexEquiv (weightDiagram μ) =
      coordinateDiagram (indexedWeightCoordinates pairing base baseIndexEquiv μ) :=
  (indexedWeightCoordinates pairing base baseIndexEquiv).apply_symm_apply _

theorem weightDiagram_involutive : Function.Involutive weightDiagram := by
  intro μ
  apply (indexedWeightCoordinates pairing base baseIndexEquiv).injective
  rw [weightDiagram_coordinates, weightDiagram_coordinates]
  funext i
  exact congrArg (indexedWeightCoordinates pairing base baseIndexEquiv μ)
    (simpleNode_involutive i)

theorem weightDiagram_fundamental (i : Fin 6) :
    weightDiagram (fundamentalWeights pairing base (baseIndexEquiv i)) =
      fundamentalWeights pairing base (baseIndexEquiv (simpleNode i)) := by
  apply (indexedWeightCoordinates pairing base baseIndexEquiv).injective
  rw [weightDiagram_coordinates]
  funext j
  have he : simpleNode j = i ↔ j = simpleNode i := simpleNode_involutive.eq_iff
  simp only [coordinateDiagram_apply,
    indexedWeightCoordinates_apply, fundamentalWeights_pairing,
    baseIndexEquiv.injective.eq_iff, he]

theorem coordinateDiagram_residue (v : Fin 6 → ℤ) :
    E6Minuscule.labelResidue (coordinateDiagram v) = -E6Minuscule.labelResidue v := by
  change (v 5 : ZMod 3) + 2 * (v 4 : ZMod 3) + (v 2 : ZMod 3) + 2 * (v 0 : ZMod 3) =
    -((v 0 : ZMod 3) + 2 * (v 2 : ZMod 3) + (v 4 : ZMod 3) + 2 * (v 5 : ZMod 3))
  rw [show (2 : ZMod 3) = -1 by decide]
  ring

theorem weightDiagram_residue (μ : WeightLattice pairing) :
    E6Minuscule.residue (weightDiagram μ) = -E6Minuscule.residue μ := by
  change E6Minuscule.labelResidue
    (indexedWeightCoordinates pairing base baseIndexEquiv (weightDiagram μ)) = _
  rw [weightDiagram_coordinates, coordinateDiagram_residue]
  rfl

theorem weightDiagram_mem_rootLattice_iff (μ : WeightLattice pairing) :
    weightDiagram μ ∈ rootLattice pairing ↔ μ ∈ rootLattice pairing := by
  rw [E6Minuscule.rootLattice_eq_residue_ker]
  change E6Minuscule.residue (weightDiagram μ) = 0 ↔ E6Minuscule.residue μ = 0
  rw [weightDiagram_residue, neg_eq_zero]

end Atlas.Chevalley.TwistedE6
