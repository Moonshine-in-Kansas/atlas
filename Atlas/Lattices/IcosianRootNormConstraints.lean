import Atlas.Lattices.IcosianGlueFreeCoordinates
import Atlas.Algebra.IcosianNormDiscriminant
import Atlas.Algebra.IcosianReductionNorm

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators Quaternion QuadraticAlgebra

/-- A zero block forces all three reductions into the rank-one row ideal. -/
theorem icosianLeechModule_zero_row (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule) (i : Fin 3) (hi : x i=0) :
    ∀ k j,icosianModuloTwo (x k) 1 j=0 := by
  have h := (icosianMatrixGlue_constraints _).mp
    ((icosianLeechModule_matrix_glue x).mp hx)
  intro k j
  have hz : icosianModuloTwo (x i) 1 j=0 := by rw [hi,map_zero]; rfl
  have h01 := (h j).1
  have h12 := (h j).2.1
  fin_cases i <;> fin_cases k <;> simp_all

theorem icosianLeechModule_zero_even_norms (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule) (i : Fin 3) (hi : x i=0) (k : Fin 3) :
    2∣(icosianIntegralNorm (x k)).re ∧ 2∣(icosianIntegralNorm (x k)).im := by
  apply (goldenModuloTwo_eq_zero _).mp
  rw [← icosianModuloTwo_det,Matrix.det_fin_two]
  simp [icosianLeechModule_zero_row x hx i hi k]

/-- The quaternionic root norm is equivalent to the exact integral golden
norm sum four, not merely a rational trace condition. -/
theorem icosianRoot_integral_norm_sum (x : IcosianCoordinates)
    (hx : icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding x)=2) :
    (∑ i,icosianIntegralNorm (x i))=4 := by
  apply goldenIntegerToRational_injective
  have hs : (∑ i,icosianNorm (x i).val)=4 := by
    have h := congrArg (fun z : IcosianQuaternion => z.re) hx
    have hg : (1/2 : ℚ) • (∑ i,icosianNorm (x i).val)=(2 : GoldenRational) := by
      simpa [icosianHermitian,icosianCoordinateEmbedding,Quaternion.star_mul_self,
        Fin.sum_univ_succ,icosianNorm,QuaternionAlgebra.re_ofNat] using h
    calc
      (∑ i,icosianNorm (x i).val) = (2 : ℚ) • ((1/2 : ℚ) •
          (∑ i,icosianNorm (x i).val)) := by simp [smul_smul]
      _ = (2 : ℚ) • (2 : GoldenRational) := by rw [hg]
      _ = 4 := by ext <;> norm_num
  simpa only [map_sum,icosianIntegralNorm_spec,map_ofNat] using hs

end Atlas.Lattices
