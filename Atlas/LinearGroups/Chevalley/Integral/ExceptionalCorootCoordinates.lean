import Atlas.LinearGroups.Chevalley.Integral.WeightCoordinates
import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.E7

/-! Actual coroot expansions. The E6 representative
extension and E7 full root evaluation require no candidate orbit assumptions. -/
set_option maxRecDepth 32768
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) (b : P.Base) {n : ℕ} (e : Fin n ≃ b.support)

@[simp] theorem corootBasis_coe (j : b.support) :
    (corootBasis P b j : N) = P.coroot j := by
  exact b.flip.coe_toWeightBasisInt_apply (⟨j.val, j.property⟩ : b.flip.support)

theorem corootElement_eq_sum_of_ambient (a : ι) (c : Fin n → ℤ)
    (hc : P.coroot a = ∑ i : Fin n, c i • P.coroot (e i)) :
    corootElement P a = ∑ i : Fin n, c i • corootBasis P b (e i) := by
  apply Subtype.ext
  simpa only [corootElement, Submodule.coe_sum, Submodule.coe_smul,
    corootBasis_coe, RootPairing.flip_root] using hc

end Atlas.Chevalley.Integral.Minuscule

namespace Atlas.Chevalley.E6Data
open Integral.Minuscule

theorem coroot_basis_expansion (a : Root) :
    corootElement pairing a = ∑ i : Fin 6, a.val (nodeEquiv.symm i) •
      corootBasis pairing base (baseIndexEquiv i) := by
  apply corootElement_eq_sum_of_ambient pairing base baseIndexEquiv
  change polar a.val = ∑ i : Fin 6, a.val (nodeEquiv.symm i) •
    polar (Pi.single (nodeEquiv.symm i) 1)
  have hx : (∑ i : Fin 6, a.val (nodeEquiv.symm i) •
      (Pi.single (nodeEquiv.symm i) (1 : ℤ))) = a.val := by
    calc
      _ = ∑ i : Fin 6, a.val i • (Pi.single i (1 : ℤ)) :=
        nodeEquiv.symm.sum_comp (fun i => a.val i • (Pi.single i (1 : ℤ)))
      _ = a.val := by ext k; simp [Finset.sum_apply, Pi.single_apply]
  have hp := congrArg polar hx
  simpa only [map_sum, map_smul] using hp.symm

theorem weight_labels_coroot_evaluation (v : Fin 6 → ℤ) (a : Root) :
    weightOfLabels pairing base baseIndexEquiv v (corootElement pairing a) =
      ∑ i : Fin 6, v i * a.val (nodeEquiv.symm i) :=
  weightOfLabels_coroot_evaluation pairing base baseIndexEquiv v _ a
    (coroot_basis_expansion a)

/-- Every actual E6 coroot is covered by the 36 opposite-pair representatives.
The finite hypothesis is an arithmetic grade condition, not a minuscule conclusion. -/
theorem weight_labels_minuscule_of_representatives (v : Fin 6 → ℤ)
    (h : ∀ r : Fin 36,
      (∑ i : Fin 6, v i *
        Atlas.Comparisons.E6Lattice.rootRepresentative r (nodeEquiv.symm i)) = -1 ∨
      (∑ i : Fin 6, v i *
        Atlas.Comparisons.E6Lattice.rootRepresentative r (nodeEquiv.symm i)) = 0 ∨
      (∑ i : Fin 6, v i *
        Atlas.Comparisons.E6Lattice.rootRepresentative r (nodeEquiv.symm i)) = 1)
    (a : Root) :
    weightOfLabels pairing base baseIndexEquiv v (corootElement pairing a) = -1 ∨
    weightOfLabels pairing base baseIndexEquiv v (corootElement pairing a) = 0 ∨
    weightOfLabels pairing base baseIndexEquiv v (corootElement pairing a) = 1 := by
  rw [weight_labels_coroot_evaluation]
  obtain ⟨r, hr | hr⟩ := Atlas.Comparisons.E6Lattice.root_representative_exhaustion a.val a.property
  · rw [hr]
    exact h r
  · rw [hr]
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rcases h r with h | h | h <;> simp [h]

end Atlas.Chevalley.E6Data

namespace Atlas.Chevalley.E7Data
open Integral.Minuscule

theorem coroot_basis_expansion (a : Root) :
    corootElement pairing a = ∑ i : Fin 7, E7Table.coordinates a i •
      corootBasis pairing base (baseIndexEquiv i) := by
  apply corootElement_eq_sum_of_ambient pairing base baseIndexEquiv
  change datum.form (datum.root a) = ∑ i : Fin 7, E7Table.coordinates a i •
    datum.form (datum.root (datum.simpleIndex i))
  simp only [datum.simple_coordinates]
  have hroot : datum.root a = E7Table.coordinates a := rfl
  rw [hroot]
  have hx : (∑ i : Fin 7, E7Table.coordinates a i • (Pi.single i (1 : ℤ))) =
      E7Table.coordinates a := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hp := congrArg datum.form hx
  simpa only [map_sum, map_smul] using hp.symm

theorem weight_labels_coroot_evaluation (v : Fin 7 → ℤ) (a : Root) :
    weightOfLabels pairing base baseIndexEquiv v (corootElement pairing a) =
      ∑ i : Fin 7, v i * E7Table.coordinates a i :=
  weightOfLabels_coroot_evaluation pairing base baseIndexEquiv v _ a
    (coroot_basis_expansion a)

end Atlas.Chevalley.E7Data
