import Atlas.Algebra.IcosianNormTwoAssociates
import Atlas.Algebra.IcosianParityIntegral
import Atlas.Algebra.IcosianModuloTwoCoordinates
import Atlas.Algebra.GoldenFourFinite

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra Quaternion BigOperators

def icosianNormTwoRepresentativeCoordinates : Fin 5 → IcosianIntegerCoordinates :=
  ![![-2,0,-2,0,0,0,0,0],![-2,0,-1,0,1,-1,0,-1],![-2,0,-1,0,1,-1,0,1],
    ![-2,0,-1,0,-1,1,0,-1],![-2,0,-1,0,-1,1,0,1]]

def icosianNormTwoRepresentative (i : Fin 5) : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients (icosianNormTwoRepresentativeCoordinates i))

def icosianNormTwoRepresentativeMatrix (i : Fin 5) : IcosianMatrix :=
  icosianMatrixFromCoefficients (fun j => goldenModuloTwo
    (icosianParityIntegralCoefficients (icosianNormTwoRepresentativeCoordinates i) j))

theorem icosianNormTwoRepresentative_reduction (i : Fin 5) :
    icosianModuloTwo (icosianNormTwoRepresentative i)=icosianNormTwoRepresentativeMatrix i :=
  icosianModuloTwo_synthesis _

theorem icosianNormTwoRepresentative_norm (i : Fin 5) :
    icosianNorm (icosianNormTwoRepresentative i).val=2 := by
  fin_cases i <;> decide +kernel

/-- The five reduction image lines exhaust singular two-by-two matrices.
This is a scalar F4 calculation, not an enumeration of lattice roots. -/
theorem icosianNormTwoRepresentative_cover :
    ∀ m : IcosianMatrix, Matrix.det m=0 →
      ∃ i : Fin 5,Matrix.adjugate (icosianNormTwoRepresentativeMatrix i)*m=0 := by
  decide +kernel

theorem icosianNormTwoRepresentative_separate :
    ∀ i j : Fin 5,i≠j →
      Matrix.adjugate (icosianNormTwoRepresentativeMatrix i)*icosianNormTwoRepresentativeMatrix j≠0 := by
  decide +kernel

end Atlas.Algebra
