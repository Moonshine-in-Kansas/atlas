import Atlas.Lattices.ConwayWales.SeedPairings

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

theorem quaternionPair_generator_lattice (t : Fin 3) (d : Row) (u : Fin 4)
    (w : Space) (hw : w ∈ seedLattice) :
    quaternionPair (seedGenerator t d u) w ∈ gaussianOrder := by
  change w ∈ Submodule.span GaussianInt _ at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨s,e,z⟩,rfl⟩ := hw
    exact quaternionPair_seed_generators t s d e u z
  | zero => simp [quaternionPair]
  | add x y hx hy ihx ihy =>
    rw [quaternionPair_add_right]
    exact gaussianOrder.add_mem ihx ihy
  | smul z x hx ih =>
    change quaternionPair _ (GaussianInt.toComplex z • x) ∈ gaussianOrder
    rw [quaternionPair_smul_right]
    exact gaussianOrder_smul ⟨z,rfl⟩ ih

theorem quaternionPair_lattice (v w : Space) (hv : v ∈ seedLattice) (hw : w ∈ seedLattice) :
    quaternionPair v w ∈ gaussianOrder := by
  change v ∈ Submodule.span GaussianInt _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨t,d,u⟩,rfl⟩ := hv
    exact quaternionPair_generator_lattice t d u w hw
  | zero =>
    have hz : dagger (0 : Q) = 0 := by ext <;> simp [dagger]
    simp only [quaternionPair, Pi.zero_apply, hz, zero_mul, Finset.sum_const_zero]
    exact gaussianOrder.zero_mem
  | add x y hx hy ihx ihy =>
    rw [quaternionPair_add_left]
    exact gaussianOrder.add_mem ihx ihy
  | smul z x hx ih =>
    change quaternionPair (GaussianInt.toComplex z • x) w ∈ gaussianOrder
    rw [quaternionPair_smul_left]
    exact gaussianOrder_smul (gaussian_star ⟨z,rfl⟩) ih

theorem hermitian_eq_quaternionPair_re (v w : Space) :
    hermitian v w = (quaternionPair v w).re := by
  simp [hermitian, quaternionPair, Fin.sum_univ_succ]
  ring

/-- Gaussian integrality of the actual seed module, before duality or S-invariance. -/
theorem seedLattice_gaussian_integral (v w : Space)
    (hv : v ∈ seedLattice) (hw : w ∈ seedLattice) : hermitian v w ∈ gaussianIntegers := by
  rw [hermitian_eq_quaternionPair_re]
  exact (quaternionPair_lattice v w hv hw).1

end Atlas.ConwayWales
