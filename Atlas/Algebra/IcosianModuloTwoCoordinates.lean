import Atlas.Algebra.IcosianModuloTwo

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra
attribute [local irreducible] icosianIntegralCoefficients goldenModuloTwo

theorem icosianModuloTwo_synthesis (a : Fin 4 → GoldenInteger) :
    icosianModuloTwo (icosianIntegralSynthesis a)=
      icosianMatrixFromCoefficients (fun i => goldenModuloTwo (a i)) := by
  have he : icosianIntegralCoefficients (icosianIntegralSynthesis a)=a :=
    icosianIntegralEquiv.apply_symm_apply a
  change icosianMatrixFromCoefficients (icosianReducedCoefficients _)=_
  apply congrArg icosianMatrixFromCoefficients
  funext i
  change goldenModuloTwo (icosianIntegralCoefficients _ i)=_
  rw [he]

/-- Computational interface using any verified integral coefficient tuple. -/
theorem icosianModuloTwo_of_coefficients (x : icosianOrder) (a : Fin 4 → GoldenInteger)
    (ha : ∀ i,goldenIntegerToRational (a i)=icosianBasisCoefficients x.val i) :
    icosianModuloTwo x=icosianMatrixFromCoefficients (fun i => goldenModuloTwo (a i)) := by
  have he : icosianIntegralCoefficients x=a := by
    funext i
    apply goldenIntegerToRational_injective
    rw [icosianIntegralCoefficients_spec,ha]
  change icosianMatrixFromCoefficients (icosianReducedCoefficients x)=_
  apply congrArg icosianMatrixFromCoefficients
  funext i
  change goldenModuloTwo (icosianIntegralCoefficients _ i)=_
  rw [he]

end Atlas.Algebra
