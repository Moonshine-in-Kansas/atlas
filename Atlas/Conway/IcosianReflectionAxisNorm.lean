import Atlas.Conway.IcosianAxisReflections
import Atlas.Conway.IcosianRootPointAction

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion

theorem icosianHermitian_two_axis (r : IcosianRationalCoordinates) (i : Fin 3) :
    icosianHermitian r (Pi.single i 2)=star (r i) := by
  rw [← icosianHermitian_star,icosianHermitian_axis_two]

theorem icosianReflection_axis_apply (r : IcosianRationalCoordinates) (i j : Fin 3) :
    icosianReflection r (Pi.single i 2) j=
      (if j=i then 2 else 0)-r j*star (r i) := by
  simp [icosianReflection,icosianHermitian_two_axis,icosianRightMul,Pi.single_apply]

theorem icosianReflection_axis_norm (r : IcosianRationalCoordinates) (i j : Fin 3) :
    icosianNorm (icosianReflection r (Pi.single i 2) j)=
      if j=i then (2-icosianNorm (r i))^2 else icosianNorm (r j)*icosianNorm (r i) := by
  rw [icosianReflection_axis_apply]
  by_cases h : j=i
  · subst j
    simp only [ite_true,Quaternion.self_mul_star]
    have he : (2 : IcosianQuaternion)-(icosianNorm (r i) : IcosianQuaternion)=
        ((2-icosianNorm (r i) : GoldenRational) : IcosianQuaternion) := by
      rw [Quaternion.coe_sub]
      exact congrArg (fun z : IcosianQuaternion => z-(icosianNorm (r i) : IcosianQuaternion))
        (Quaternion.coe_natCast (R := GoldenRational) 2).symm
    change icosianNorm ((2 : IcosianQuaternion)-(icosianNorm (r i) : IcosianQuaternion))=
      (2-icosianNorm (r i))^2
    rw [he]
    exact Quaternion.normSq_coe _
  · simp only [h,ite_false,zero_sub]
    simp only [icosianNorm,Quaternion.normSq_neg,map_mul,Quaternion.normSq_star]

end Atlas.Conway
