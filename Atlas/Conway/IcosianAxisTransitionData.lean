import Atlas.Conway.IcosianReflectionIsometries
import Atlas.Lattices.IcosianGlueFreeCoordinates
import Atlas.Algebra.IcosianParityIntegral

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix Quaternion QuadraticAlgebra

/-- Four local roots: one (2,1,1) root and three roots orthogonal to axis zero.
Only these displayed coordinates enter the local transition proofs. -/
def icosianAxisTransitionRootData : Fin 4 → Fin 3 → IcosianIntegerCoordinates :=
  ![![![-2,0,-1,0,-1,1,0,1],![0,0,1,0,-1,1,0,1],![0,0,1,0,-1,1,0,1]],![![0,0,0,0,0,0,0,0],![-2,0,-2,0,0,0,0,0],![-2,0,2,0,0,0,0,0]],![![0,0,0,0,0,0,0,0],![-2,0,-2,0,0,0,0,0],![0,0,0,0,-2,0,-2,0]],![![0,0,0,0,0,0,0,0],![-2,0,-2,0,0,0,0,0],![0,0,0,0,-2,0,2,0]]]

attribute [local irreducible] icosianAxisTransitionRootData

def icosianAxisTransitionIntegral (k : Fin 4) : IcosianCoordinates :=
  fun i => icosianIntegralSynthesis
    (icosianParityIntegralCoefficients (icosianAxisTransitionRootData k i))

def icosianAxisTransitionRoot (k : Fin 4) : IcosianRationalCoordinates :=
  fun i => icosianCoordinatesQuaternion (icosianAxisTransitionRootData k i)

theorem icosianAxisTransitionRoot_coordinates (k : Fin 4) (i : Fin 3) :
    icosianAxisTransitionRoot k i =
      icosianCoordinatesQuaternion (icosianAxisTransitionRootData k i) := rfl

theorem icosianAxisTransitionIntegral_coordinates :
    ∀ k i, (icosianAxisTransitionIntegral k i).val =
      icosianAxisTransitionRoot k i := by
  intro k i
  fin_cases k <;> fin_cases i <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionRoot_norm :
    ∀ k, icosianHermitian (icosianAxisTransitionRoot k)
      (icosianAxisTransitionRoot k) = 2 := by
  intro k
  fin_cases k <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionIntegral_mem (k : Fin 4) :
    icosianAxisTransitionIntegral k ∈ icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  change ∀ j, _
  simp only [icosianAxisTransitionIntegral,icosianModuloTwo_synthesis]
  unfold icosianAxisTransitionRootData
  fin_cases k <;> intro j <;> fin_cases j <;> refine ⟨?_,?_,?_⟩ <;>
    apply QuadraticAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionRoot_mem (k : Fin 4) :
    icosianAxisTransitionRoot k ∈ rationalIcosianLattice :=
  ⟨icosianAxisTransitionIntegral k,icosianAxisTransitionIntegral_mem k,
    funext (icosianAxisTransitionIntegral_coordinates k)⟩

def icosianAxisTransitionGenerator (k : Fin 4) : icosianHermitianGroup :=
  icosianRootReflection (icosianAxisTransitionRoot k)
    (icosianAxisTransitionRoot_norm k) (icosianAxisTransitionRoot_mem k)

end Atlas.Conway
