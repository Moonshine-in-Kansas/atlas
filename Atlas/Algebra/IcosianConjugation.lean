import Atlas.Algebra.IcosianOrderBasis

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

theorem icosianBasisCoefficients_star (x : IcosianQuaternion) :
    icosianBasisCoefficients (star x)=
      ![icosianBasisCoefficients x 0+icosianBasisCoefficients x 2-
          goldenSigma*icosianBasisCoefficients x 3,
        -icosianBasisCoefficients x 1,-icosianBasisCoefficients x 2,
        -icosianBasisCoefficients x 3] := by
  funext i
  fin_cases i <;> ext <;> simp [icosianBasisCoefficients,goldenSigma,
    goldenTau,QuadraticAlgebra.omega,pow_two] <;> ring

theorem icosianOrder_star_mem {x : IcosianQuaternion} (hx : x ∈ icosianOrder) :
    star x ∈ icosianOrder := by
  have hs : goldenSigma ∈ goldenIntegerToRational.range :=
    ⟨1-QuadraticAlgebra.omega,by ext <;>
      simp [goldenIntegerToRational,goldenSigma,goldenTau,QuadraticAlgebra.omega]⟩
  intro i
  rw [icosianBasisCoefficients_star]
  fin_cases i
  · exact goldenIntegerToRational.range.sub_mem
      (goldenIntegerToRational.range.add_mem (hx 0) (hx 2))
      (goldenIntegerToRational.range.mul_mem hs (hx 3))
  · exact goldenIntegerToRational.range.neg_mem (hx 1)
  · exact goldenIntegerToRational.range.neg_mem (hx 2)
  · exact goldenIntegerToRational.range.neg_mem (hx 3)

end Atlas.Algebra
