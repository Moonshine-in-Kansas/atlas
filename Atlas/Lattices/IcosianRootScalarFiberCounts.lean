import Atlas.Lattices.IcosianRootNormFibers
import Atlas.Algebra.IcosianUnitNormFibers

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra

theorem icosianScalarNorm_one_fiber_card (m : IcosianMatrix) (hm : Matrix.det m=1) :
    Nat.card (IcosianScalarNormReductionFiber 1 m)=2 := by
  rw [Nat.card_congr (icosianScalarNormReductionFiberEquiv 1 m)]
  have h := icosianGoldenUnitNormFiber_card (1 : GoldenIntegerˣ) m (by simpa using hm)
  have he : goldenIntegerToRational ((1 : GoldenIntegerˣ) : GoldenInteger)=1 := rfl
  unfold IcosianNormShell at h
  rw [he, one_pow] at h
  exact h

theorem icosianScalarNorm_tau_fiber_card (m : IcosianMatrix)
    (hm : Matrix.det m=goldenFourTau^2) :
    Nat.card (IcosianScalarNormReductionFiber (goldenTau^2) m)=2 := by
  rw [Nat.card_congr (icosianScalarNormReductionFiberEquiv _ m)]
  exact icosianGoldenUnitNormFiber_card goldenTauUnit m hm

theorem icosianScalarNorm_sigma_fiber_card (m : IcosianMatrix)
    (hm : Matrix.det m=(1-goldenFourTau)^2) :
    Nat.card (IcosianScalarNormReductionFiber (goldenSigma^2) m)=2 := by
  rw [Nat.card_congr (icosianScalarNormReductionFiberEquiv _ m)]
  have he : goldenIntegerToRational (goldenSigmaUnit : GoldenInteger)=goldenSigma := by
    ext <;> norm_num [goldenSigmaUnit, goldenSigma, goldenTau, goldenIntegerToRational, QuadraticAlgebra.omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h := icosianGoldenUnitNormFiber_card goldenSigmaUnit m hm
  unfold IcosianNormShell at h
  rw [he] at h
  exact h

theorem icosianScalarNorm_two_fiber_card (m : IcosianMatrix)
    (hm : Matrix.det m=0) (hne : m≠0) :
    Nat.card (IcosianScalarNormReductionFiber 2 m)=8 := by
  rw [Nat.card_congr (icosianScalarNormReductionFiberEquiv 2 m)]
  exact icosianNormTwoReduction_fiber_card m hm hne

end Atlas.Lattices
