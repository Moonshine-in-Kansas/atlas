import Atlas.Algebra.IcosianNormTwoCount

noncomputable section
namespace Atlas.Algebra
open scoped Matrix

abbrev IcosianSpecialLinear := Matrix.SpecialLinearGroup (Fin 2) GoldenFour

abbrev IcosianNormTwoMatrixParameters (m : IcosianMatrix) :=
  {p : Fin 5 × IcosianSpecialLinear //
    icosianNormTwoRepresentativeMatrix p.1 * (p.2 : IcosianMatrix) = m}

/-- Each nonzero singular scalar matrix has four lifted special-linear
coordinates among the five projective image-line representatives. -/
theorem icosianNormTwoMatrixParameters_count :
    ∀ m : IcosianMatrix, Matrix.det m = 0 → m ≠ 0 →
      Fintype.card (IcosianNormTwoMatrixParameters m) = 4 := by
  decide +kernel

end Atlas.Algebra
