import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Spanning
import Atlas.Algebra.CyclicLatticeQuotient
import Mathlib.Data.ZMod.Basic

/-! Exact order-two character and identification of the actual E7 quotient P/Q.
No group-center statement follows here without a separate representation theorem. -/
noncomputable section
namespace Atlas.Chevalley.E7Minuscule
open Integral.Minuscule E7Data
open scoped BigOperators
local notation "P" => E7Data.pairing
local notation "b" => E7Data.base
local notation "e" => E7Data.baseIndexEquiv

/-- Reduction modulo two of the three odd fundamental-weight coordinates. -/
def labelParity : (Fin 7 → ℤ) →ₗ[ℤ] ZMod 2 where
  toFun v := (v 1 : ZMod 2) + (v 4 : ZMod 2) + (v 6 : ZMod 2)
  map_add' v w := by simp only [Pi.add_apply, Int.cast_add]; abel
  map_smul' z v := by simp [Int.cast_mul, smul_eq_mul, mul_add]

def parity : Weight →ₗ[ℤ] ZMod 2 := labelParity.comp (indexedWeightCoordinates P b e).toLinearMap

theorem simple_labelParity : ∀ i : Fin 7,
    labelParity (fun j => CartanMatrix.E 7 i j) = 0 := by decide +kernel

theorem root_parity (r : E7Data.Root) : parity (rootWeight P r) = 0 := by
  have hx : indexedWeightCoordinates P b e (rootWeight P r) =
      ∑ i : Fin 7, E7Table.coordinates r i • (fun j => CartanMatrix.E 7 i j) := by
    ext j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using root_coordinates r j
  change labelParity (indexedWeightCoordinates P b e (rootWeight P r)) = 0
  rw [hx, map_sum]
  simp only [map_smul, simple_labelParity, smul_zero, Finset.sum_const_zero]

theorem rootLattice_le_parity_ker : rootLattice P ≤ LinearMap.ker parity := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact root_parity r

theorem selected_parity : parity selectedWeight = 1 := by
  rw [show selectedWeight = weightOfLabels P b e
    (Pi.single E7MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm]
  change labelParity ((indexedWeightCoordinates P b e)
    ((indexedWeightCoordinates P b e).symm _)) = 1
  rw [LinearEquiv.apply_symm_apply]
  decide +kernel

/-- Integral coefficients of twice the selected fundamental weight in Q. -/
def doubleCoefficients : Fin 7 → ℤ := ![2,3,4,6,5,4,3]

theorem double_coordinates : ∀ j : Fin 7,
    (∑ i : Fin 7, doubleCoefficients i * CartanMatrix.E 7 i j) =
      2 * (Pi.single E7MinusculeTable.selectedNode 1 : Fin 7 → ℤ) j := by decide +kernel

theorem selected_double_mem : (2 : ℤ) • selectedWeight ∈ rootLattice P := by
  have hx : (2 : ℤ) • selectedWeight =
      ∑ i : Fin 7, doubleCoefficients i • rootWeight P (e i) := by
    apply (indexedWeightCoordinates P b e).injective
    rw [show selectedWeight = weightOfLabels P b e
      (Pi.single E7MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm]
    ext j
    simp only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      indexedSimpleRootWeight_coordinates, E7Data.base_cartan]
    simpa only [indexedWeightCoordinates_apply, weightOfLabels_simple_evaluation]
      using (double_coordinates j).symm
  rw [hx]
  exact (rootLattice P).sum_mem (fun i _ =>
    (rootLattice P).smul_mem _ (rootWeight_mem_rootLattice P (e i)))

theorem selected_not_mem : selectedWeight ∉ rootLattice P := by
  intro h
  have hp : parity selectedWeight = 0 := rootLattice_le_parity_ker h
  rw [selected_parity] at hp
  exact one_ne_zero hp

theorem rootLattice_eq_parity_ker : rootLattice P = LinearMap.ker parity :=
  (Atlas.Algebra.latticeCharacter_ker_eq (rootLattice P) selectedWeight 2 parity
    rootLattice_le_parity_ker rootLattice_sup_selected selected_parity selected_double_mem).symm

/-- Explicit identification of the actual weight/root quotient with Z/2. -/
def weightRootQuotientEquiv : (Weight ⧸ rootLattice P) ≃ₗ[ℤ] ZMod 2 :=
  Atlas.Algebra.cyclicLatticeQuotientEquiv (rootLattice P) selectedWeight 2 parity
    rootLattice_le_parity_ker rootLattice_sup_selected selected_parity selected_double_mem

@[simp] theorem weightRootQuotientEquiv_selected :
    weightRootQuotientEquiv (Submodule.Quotient.mk selectedWeight) = 1 :=
  selected_parity

theorem weightRootQuotient_card : Nat.card (Weight ⧸ rootLattice P) = 2 :=
  Atlas.Algebra.cyclicLatticeQuotient_card (rootLattice P) selectedWeight 2 parity
    rootLattice_le_parity_ker rootLattice_sup_selected selected_parity selected_double_mem

end Atlas.Chevalley.E7Minuscule
