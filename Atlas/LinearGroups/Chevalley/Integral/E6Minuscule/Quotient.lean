import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Spanning
import Atlas.Algebra.CyclicLatticeQuotient
import Mathlib.Data.ZMod.Basic

/-! Actual E6 weight/root quotient, via an explicit character modulo three.
This is a lattice theorem, not a group-center identification. -/
noncomputable section
namespace Atlas.Chevalley.E6Minuscule
open Integral.Minuscule E6Data
open scoped BigOperators
local notation "P" => E6Data.pairing
local notation "b" => E6Data.base
local notation "e" => E6Data.baseIndexEquiv

def labelResidue : (Fin 6 → ℤ) →ₗ[ℤ] ZMod 3 where
  toFun v := (v 0 : ZMod 3) + 2 * (v 2 : ZMod 3) + (v 4 : ZMod 3) + 2 * (v 5 : ZMod 3)
  map_add' v w := by simp only [Pi.add_apply, Int.cast_add, mul_add]; abel
  map_smul' z v := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply]
    ring

def residue : Weight →ₗ[ℤ] ZMod 3 :=
  labelResidue.comp (indexedWeightCoordinates P b e).toLinearMap

theorem simple_labelResidue : ∀ i : Fin 6,
    labelResidue (fun j => CartanMatrix.E 6 i j) = 0 := by decide +kernel

theorem root_residue (r : E6Data.Root) : residue (rootWeight P r) = 0 := by
  have hx : indexedWeightCoordinates P b e (rootWeight P r) =
      ∑ i : Fin 6, r.val (E6Data.nodeEquiv.symm i) • (fun j => CartanMatrix.E 6 i j) := by
    ext j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using root_coordinates r j
  change labelResidue (indexedWeightCoordinates P b e (rootWeight P r)) = 0
  rw [hx, map_sum]
  simp only [map_smul, simple_labelResidue, smul_zero, Finset.sum_const_zero]

theorem rootLattice_le_residue_ker : rootLattice P ≤ LinearMap.ker residue := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact root_residue r

theorem selected_residue : residue selectedWeight = 1 := by
  rw [show selectedWeight = weightOfLabels P b e
    (Pi.single E6MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm]
  change labelResidue ((indexedWeightCoordinates P b e)
    ((indexedWeightCoordinates P b e).symm _)) = 1
  rw [LinearEquiv.apply_symm_apply]
  decide +kernel

def tripleCoefficients : Fin 6 → ℤ := ![4,3,5,6,4,2]

theorem triple_coordinates : ∀ j : Fin 6,
    (∑ i : Fin 6, tripleCoefficients i * CartanMatrix.E 6 i j) =
      3 * (Pi.single E6MinusculeTable.selectedNode 1 : Fin 6 → ℤ) j := by decide +kernel

theorem selected_triple_mem : (3 : ℤ) • selectedWeight ∈ rootLattice P := by
  have hx : (3 : ℤ) • selectedWeight =
      ∑ i : Fin 6, tripleCoefficients i • rootWeight P (e i) := by
    apply (indexedWeightCoordinates P b e).injective
    rw [show selectedWeight = weightOfLabels P b e
      (Pi.single E6MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm]
    ext j
    simp only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      indexedSimpleRootWeight_coordinates, E6Data.base_cartan]
    simpa only [indexedWeightCoordinates_apply, weightOfLabels_simple_evaluation]
      using (triple_coordinates j).symm
  rw [hx]
  exact (rootLattice P).sum_mem (fun i _ =>
    (rootLattice P).smul_mem _ (rootWeight_mem_rootLattice P (e i)))

theorem selected_not_mem : selectedWeight ∉ rootLattice P := by
  intro h
  have hp : residue selectedWeight = 0 := rootLattice_le_residue_ker h
  rw [selected_residue] at hp
  exact one_ne_zero hp

theorem rootLattice_eq_residue_ker : rootLattice P = LinearMap.ker residue :=
  (Atlas.Algebra.latticeCharacter_ker_eq (rootLattice P) selectedWeight 3 residue
    rootLattice_le_residue_ker rootLattice_sup_selected selected_residue selected_triple_mem).symm

def weightRootQuotientEquiv : (Weight ⧸ rootLattice P) ≃ₗ[ℤ] ZMod 3 :=
  Atlas.Algebra.cyclicLatticeQuotientEquiv (rootLattice P) selectedWeight 3 residue
    rootLattice_le_residue_ker rootLattice_sup_selected selected_residue selected_triple_mem

@[simp] theorem weightRootQuotientEquiv_selected :
    weightRootQuotientEquiv (Submodule.Quotient.mk selectedWeight) = 1 := selected_residue

theorem weightRootQuotient_card : Nat.card (Weight ⧸ rootLattice P) = 3 :=
  Atlas.Algebra.cyclicLatticeQuotient_card (rootLattice P) selectedWeight 3 residue
    rootLattice_le_residue_ker rootLattice_sup_selected selected_residue selected_triple_mem

end Atlas.Chevalley.E6Minuscule
