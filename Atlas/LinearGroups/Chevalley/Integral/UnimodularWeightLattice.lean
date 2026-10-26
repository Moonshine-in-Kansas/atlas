import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The integral root lattice equals the full weight lattice when the actual
Cartan matrix is unimodular. This is a lattice theorem, not a center theorem. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base) [P.IsCrystallographic]

/-- Integer invertibility of the actual simple-root coordinate matrix implies
that the roots span the entire full weight lattice. -/
theorem rootLattice_eq_top_of_cartan_isUnit_det {n : ℕ}
    (e : Fin n ≃ b.support) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : ∀ i j, b.cartanMatrix (e i) (e j) = C i j)
    (hdet : IsUnit C.det) : rootLattice P = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro μ
  have hsurj : Function.Surjective C.vecMul :=
    Matrix.vecMul_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr hdet)
  obtain ⟨c, hc⟩ := hsurj (fun j => weightCoordinates P b μ (e j))
  have he : ∑ i : Fin n, c i • rootWeight P (e i) = μ := by
    apply (weightCoordinates P b).injective
    funext j
    obtain ⟨j, rfl⟩ := e.surjective j
    have hj := congrFun hc j
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, simpleRootWeight_coordinates, hC, Matrix.vecMul, dotProduct] using hj
  rw [← he]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (rootWeight_mem_rootLattice P (e i)))

end Atlas.Chevalley.Integral.Minuscule

