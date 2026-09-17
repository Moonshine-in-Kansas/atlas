import Atlas.Conway.IcosianRootPointShapes
import Atlas.Conway.IcosianReflectionDiagonalData

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix Quaternion QuadraticAlgebra

/-- A scalar norm-two icosian making the mixed root `(q,1,1)` integral. -/
def icosianLocalCScalarCoordinates : IcosianIntegerCoordinates := ![1,0,1,0,-1,0,-1,2]

def icosianLocalCScalar : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients icosianLocalCScalarCoordinates)

theorem icosianLocalCScalar_norm : icosianNorm icosianLocalCScalar.val=2 := by
  decide +kernel

theorem icosianLocalCScalar_reduction : icosianModuloTwo icosianLocalCScalar=!![0,0;0,1] := by
  rw [icosianLocalCScalar,icosianModuloTwo_synthesis]
  decide +kernel

def icosianLocalCVector : IcosianCoordinates := ![icosianLocalCScalar,1,1]

theorem icosianLocalCVector_mem : icosianLocalCVector∈icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  intro j
  fin_cases j <;> simp [icosianLocalCVector,icosianLocalCScalar_reduction]
  apply QuadraticAlgebra.ext <;> decide +kernel

theorem icosianLocalCVector_norm :
    icosianHermitian (icosianCoordinateEmbedding icosianLocalCVector)
      (icosianCoordinateEmbedding icosianLocalCVector)=2 := by
  apply QuaternionAlgebra.ext <;> decide +kernel

def icosianLocalCRoot : IcosianRoot :=
  ⟨icosianLocalCVector,icosianLocalCVector_mem,icosianLocalCVector_norm⟩

theorem icosianLocalCRoot_shape : HasIcosianRootShape icosianLocalCRoot 2 := by
  apply (icosianRootShape_c _).mpr
  apply icosianRootC_recognition _ 0
  intro j
  apply icosianRootNormWord_of_norm
  fin_cases j
  · change icosianNorm icosianLocalCScalar.val=goldenIntegerToRational 2
    simpa only [map_ofNat] using icosianLocalCScalar_norm
  · change icosianNorm (1 : IcosianQuaternion)=goldenIntegerToRational 1
    rw [map_one]
    exact icosianNormOneGroup_norm 1
  · change icosianNorm (1 : IcosianQuaternion)=goldenIntegerToRational 1
    rw [map_one]
    exact icosianNormOneGroup_norm 1

/-- The already verified first reflection root is a reference for the three
pairwise distinct golden coordinate norms. -/
def icosianLocalDRoot : IcosianRoot :=
  ⟨icosianReflectionDiagonalIntegral 0,icosianReflectionDiagonalIntegral_mem 0,by
    have he : icosianCoordinateEmbedding (icosianReflectionDiagonalIntegral 0)=
        icosianReflectionDiagonalRoot 0 := funext (icosianReflectionDiagonalIntegral_coordinates 0)
    rw [he]
    exact icosianReflectionDiagonalRoot_norm 0⟩

theorem icosianLocalDRoot_norm_word :
    icosianRootNormWord icosianLocalDRoot=![((1-ω)^2 : GoldenInteger),ω^2,1] := by
  funext i
  apply icosianRootNormWord_of_norm
  change icosianNorm ((icosianReflectionDiagonalIntegral 0 i).val)=_
  rw [icosianReflectionDiagonalIntegral_coordinates]
  fin_cases i <;> decide +kernel

theorem icosianLocalDRoot_shape : HasIcosianRootShape icosianLocalDRoot 3 := by
  change List.Perm _ [1,(ω : GoldenInteger)^2,(1-ω)^2]
  rw [icosianLocalDRoot_norm_word]
  exact Atlas.triple_perm_reindex (Equiv.swap 0 2) icosianRootDNorms

end Atlas.Conway
