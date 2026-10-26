import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Orbit
/-! Actual E7 minuscule weight lattice: Spanning. -/
noncomputable section
namespace Atlas.Chevalley.E7Minuscule
open Integral.Minuscule E7Data
open scoped BigOperators
local notation "P" => E7Data.pairing
local notation "b" => E7Data.base
local notation "e" => E7Data.baseIndexEquiv
local notation "T" => E7MinusculeTable.Weight
/-- The root lattice together with the chosen fundamental weight spans P. -/
theorem rootLattice_sup_selected :
    rootLattice P ⊔ Submodule.span ℤ {selectedWeight} = ⊤ := by
  apply top_unique
  intro μ _
  let S : Submodule ℤ Weight := rootLattice P ⊔ Submodule.span ℤ {selectedWeight}
  have hselected : selectedWeight ∈ S :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have hs (i : Fin 7) : rootWeight P (e i) ∈ S :=
    Submodule.mem_sup_left (rootWeight_mem_rootLattice P (e i))
  have hfund (j : Fin 7) : weightOfLabels P b e (Pi.single j 1) ∈ S := by
    have heq : (∑ i : Fin 7, E7MinusculeTable.spanningCoefficients j i • rootWeight P (e i)) +
        E7MinusculeTable.selectedMultiples j • selectedWeight =
        weightOfLabels P b e (Pi.single j 1) := by
      apply (indexedWeightCoordinates P b e).injective
      ext k
      simp only [map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, indexedSimpleRootWeight_coordinates, E7Data.base_cartan]
      rw [show selectedWeight = weightOfLabels P b e
          (Pi.single E7MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm]
      simpa only [indexedWeightCoordinates_apply, weightOfLabels_simple_evaluation] using E7MinusculeTable.weight_lattice_spanning j k
    rw [← heq]
    exact S.add_mem (S.sum_mem (fun i _ => S.smul_mem _ (hs i))) (S.smul_mem _ hselected)
  have hdecomp : μ = ∑ i : Fin 7, indexedWeightCoordinates P b e μ i •
      weightOfLabels P b e (Pi.single i 1) := by
    apply (indexedWeightCoordinates P b e).injective
    ext j
    simp [map_sum, map_smul, Finset.sum_apply, Pi.single_apply]
  rw [hdecomp]
  exact S.sum_mem (fun i _ => S.smul_mem _ (hfund i))


end Atlas.Chevalley.E7Minuscule
