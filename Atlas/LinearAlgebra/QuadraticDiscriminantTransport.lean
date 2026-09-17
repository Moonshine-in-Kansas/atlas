import Atlas.LinearAlgebra.QuadraticDeterminantClassClassification

/-! # Intrinsic discriminant classes under actual isometries -/
noncomputable section
namespace Atlas.Quadratic
variable {F V W : Type*} [Field F] [Invertible (2 : F)]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem discriminantClass_isometry (Q : QuadraticForm F V) (R : QuadraticForm F W)
    (hQ : Q.polarBilin.Nondegenerate) (hR : R.polarBilin.Nondegenerate) (e : Q.IsometryEquiv R) :
    discriminantClass Q hQ = discriminantClass R hR := by
  rw [discriminantClass_basis Q hQ (Module.finBasis F V),
    discriminantClass_basis R hR ((Module.finBasis F V).map e.toLinearEquiv)]
  symm
  apply Atlas.Bilinear.determinantClass_transport
  intro x y
  change R.associated (e x) (e y) = Q.associated x y
  simp only [QuadraticMap.associated_apply]
  have he : e (x + y) = e x + e y := e.toLinearEquiv.map_add x y
  rw [← he,e.map_app,e.map_app,e.map_app]

theorem discriminantClass_sum_squares (k : ℕ)
    (hQ : (diagonalForm (fun _ : Fin k => (1 : F))).polarBilin.Nondegenerate) :
    discriminantClass (diagonalForm (fun _ : Fin k => (1 : F))) hQ = 1 := by
  rw [discriminantClass_basis _ hQ (Pi.basisFun F (Fin k))]
  have hu : Atlas.Bilinear.gramUnit (diagonalForm (fun _ : Fin k => (1 : F))).associated
      (associated_nondegenerate _ hQ) (Pi.basisFun F (Fin k)) = 1 := by
    apply Units.ext
    change (diagonalForm (fun _ : Fin k => (1 : F))).discr' = 1
    simp [diagonal_discr]
  change Atlas.squareClass F _ = 1
  rw [hu,map_one]
end Atlas.Quadratic
