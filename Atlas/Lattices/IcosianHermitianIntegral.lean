import Atlas.Lattices.IcosianGlueFreeCoordinates
import Atlas.Codes.IcosianMatrixGluePairing
import Atlas.Algebra.IcosianReductionConjugation
import Atlas.Algebra.IcosianModuloTwoKernel
import Atlas.Lattices.IcosianReflection

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators Quaternion

theorem icosianHermitian_integral_coordinates (x y : IcosianCoordinates)
    (hx : x ∈ icosianLeechModule) (hy : y ∈ icosianLeechModule) :
    IsIcosian (icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding y)) := by
  let z : icosianOrder := ∑ i,icosianOrderStar (x i)*y i
  have hz : icosianModuloTwo z=0 := by
    simp only [z,map_sum,map_mul,icosianModuloTwo_star]
    exact icosianMatrixGlue_adjugate_pairing _ _
      ((icosianLeechModule_matrix_glue x).mp hx)
      ((icosianLeechModule_matrix_glue y).mp hy)
  obtain ⟨a,ha⟩ := (icosianModuloTwo_eq_zero_iff_two_mul z).mp hz
  have hval : (z : IcosianQuaternion)=(2 : ℚ) • a.val := by
    have h := congrArg Subtype.val ha
    simpa [two_mul,two_smul] using h
  have he : icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding y)=a.val := by
    change (1/2 : ℚ) • (z : IcosianQuaternion)=a.val
    rw [hval,smul_smul]
    norm_num
  rw [he]
  exact a.property

theorem icosianHermitian_integral {x y : IcosianRationalCoordinates}
    (hx : x ∈ rationalIcosianLattice) (hy : y ∈ rationalIcosianLattice) :
    IsIcosian (icosianHermitian x y) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact icosianHermitian_integral_coordinates a b ha hb

/-- Lattice preservation comes from integral Hermitian pairings and the actual right module. -/
theorem icosianReflection_lattice {r v : IcosianRationalCoordinates}
    (hr : r ∈ rationalIcosianLattice) (hv : v ∈ rationalIcosianLattice) :
    icosianReflection r v ∈ rationalIcosianLattice := by
  let a : icosianOrder := ⟨icosianHermitian r v,icosianHermitian_integral hr hv⟩
  obtain ⟨rr,hrr,hre⟩ := hr
  obtain ⟨vv,hvv,hve⟩ := hv
  refine ⟨vv-MulOpposite.op a • rr,
    icosianLeechModule.sub_mem hvv (icosianLeechModule.smul_mem (MulOpposite.op a) hrr),?_⟩
  change icosianCoordinateEmbedding (vv-MulOpposite.op a • rr)=v-icosianRightMul r a.val
  rw [← hre,← hve]
  rfl

end Atlas.Lattices
