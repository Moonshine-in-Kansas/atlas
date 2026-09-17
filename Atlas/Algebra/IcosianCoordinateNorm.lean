import Atlas.Algebra.IcosianUnitCandidates

namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra BigOperators

def icosianCoordinatesQuaternion (v : IcosianIntegerCoordinates) : IcosianQuaternion :=
  ⟨⟨(v 0 : ℚ)/2,(v 1 : ℚ)/2⟩,⟨(v 2 : ℚ)/2,(v 3 : ℚ)/2⟩,
    ⟨(v 4 : ℚ)/2,(v 5 : ℚ)/2⟩,⟨(v 6 : ℚ)/2,(v 7 : ℚ)/2⟩⟩

theorem icosianCoordinatesQuaternion_norm (v : IcosianIntegerCoordinates) :
    icosianNorm (icosianCoordinatesQuaternion v)=
      ⟨(icosianCoordinateNorm v : ℚ)/4,(icosianCoordinateTau v : ℚ)/4⟩ := by
  rw [icosianNorm_coordinates]
  ext <;> simp [icosianCoordinatesQuaternion,
    icosianCoordinateNorm,icosianCoordinateTau,Fin.sum_univ_succ,pow_two] <;> ring

theorem icosianNormOneCoordinates_norm {v : IcosianIntegerCoordinates}
    (hv : v ∈ icosianNormOneCoordinates) :
    icosianNorm (icosianCoordinatesQuaternion v)=1 := by
  obtain ⟨hshort,htau⟩ := Finset.mem_filter.mp hv
  rw [icosianCoordinatesQuaternion_norm,icosianShortCoordinates_norm v hshort,htau]
  ext <;> norm_num

end Atlas.Algebra
