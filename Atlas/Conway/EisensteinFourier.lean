import Atlas.Lattices.EisensteinFourierChecks
import Atlas.Lattices.EisensteinIntegralGenerators
import Atlas.Conway.EisensteinCentralizer

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped Matrix

private theorem source_generator_surjective {g : EisensteinCoordinates}
    (hg : g ∈ eisensteinGeneratorSet) :
    ∃ j,eisensteinComparisonSourceGenerator j=g := by
  rcases hg with ((rfl | ⟨j,rfl⟩) | ⟨i,rfl⟩) | rfl
  · exact ⟨0,rfl⟩
  · refine ⟨⟨j.val+1,by omega⟩,?_⟩
    simp [eisensteinComparisonSourceGenerator,show j.val+1≠0 by omega,
      show j.val+1<7 by omega]
  · refine ⟨⟨i.val+7,by omega⟩,?_⟩
    simp [eisensteinComparisonSourceGenerator,show i.val+7≠0 by omega,
      show ¬i.val+7<7 by omega,show i.val+7<19 by omega]
  · exact ⟨19,rfl⟩

theorem eisensteinFourier_direction_mem (d : Fin 2) (z : EisensteinRationalCoordinates)
    (hz : z ∈ rationalEisensteinLattice) :
    eisensteinFourierDirection d *ᵥ z ∈ rationalEisensteinLattice := by
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hz
  let f : EisensteinRationalCoordinates →ₗ[ℤ] EisensteinRationalCoordinates :=
    (Matrix.toLin' (eisensteinFourierDirection d)).restrictScalars ℤ
  let S : Submodule ℤ EisensteinCoordinates := rationalEisensteinLattice.comap
    (f.comp eisensteinCoordinateEmbedding)
  have h (p : Fin 2) (g : EisensteinCoordinates) (hg : g ∈ eisensteinGeneratorSet) :
      eisensteinComparisonPhase p • g ∈ S := by
    obtain ⟨j,rfl⟩ := source_generator_surjective hg
    exact eisensteinFourier_generator_mem d j p
  exact eisensteinLeechModule_integral_generators S
    (fun g hg => by simpa [eisensteinComparisonPhase] using h 0 g hg)
    (fun g hg => by simpa [eisensteinComparisonPhase] using h 1 g hg) hv

theorem eisensteinFourier_lattice_iff (z : EisensteinRationalCoordinates) :
    z ∈ rationalEisensteinLattice ↔ eisensteinFourier z ∈ rationalEisensteinLattice := by
  constructor
  · exact eisensteinFourier_direction_mem 0 z
  · intro hz
    have h := eisensteinFourier_direction_mem 1 (eisensteinFourier z) hz
    change eisensteinFourier.symm (eisensteinFourier z) ∈ rationalEisensteinLattice at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h

/-- The corrected Fourier operator in the full scalar-linear lattice isometry group. -/
def eisensteinFourierIsometry : eisensteinHermitianGroup :=
  ⟨eisensteinFourier,
    (fun a z => eisensteinFourierLinear.map_smul a z),
    eisensteinFourier_hermitian,eisensteinFourier_lattice_iff⟩

def eisensteinFourierCo0 : LeechIsometryGroup :=
  eisensteinHermitianToCo0 eisensteinFourierIsometry

end Atlas.Conway
