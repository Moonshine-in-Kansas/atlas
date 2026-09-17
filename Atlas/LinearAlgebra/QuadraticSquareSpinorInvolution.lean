import Atlas.LinearAlgebra.QuadraticNormalBasis
import Atlas.LinearAlgebra.QuadraticCoordinateInvolution
import Atlas.LinearAlgebra.QuadraticDiscriminantTransport
import Atlas.LinearAlgebra.QuadraticInvolutionTransport
import Atlas.LinearAlgebra.InvolutionDeterminant

/-! # Actual involutions with every prescribed even minus dimension and square spinor class -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [Finite F] [Invertible (2 : F)]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_square_spinor_involution (h2 : (2 : F) ≠ 0)
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
    (n m : ℕ) (hd : Module.finrank F V = 2 * n + 1) (hm : m ≤ n) :
    ∃ g : Q.IsometryEquiv Q, Function.Involutive g ∧
      Module.finrank F (Atlas.LinearInvolution.minus g.toLinearEquiv.toLinearMap) = 2 * m ∧
      g.toLinearEquiv.toLinearMap.det = 1 ∧ wallDeterminantClass Q hQ g = 1 := by
  obtain ⟨d,hd0,⟨e⟩⟩ := finite_nondegenerate_normal_form h2 Q hQ (2*n) hd
  let R := diagonalForm (normalWeights (2*n) d)
  let t := coordinateSignIsometry (normalWeights (2*n) d) (2*m)
  let g := conjugateIsometry R Q e.symm t
  have ht : Function.Involutive t := coordinateSign_involutive (2*n+1) (2*m)
  have hg : Function.Involutive g := conjugateIsometry_involutive R Q e.symm t ht
  have hk : 2*m ≤ 2*n+1 := by omega
  have hdim : Module.finrank F (Atlas.LinearInvolution.minus g.toLinearEquiv.toLinearMap) = 2*m := by
    rw [conjugateIsometry_finrank_minus R Q e.symm t]
    exact coordinateSign_finrank_minus _ _ hk h2
  have hdet : g.toLinearEquiv.toLinearMap.det = 1 := by
    rw [Atlas.LinearInvolution.determinant _ hg h2,hdim,pow_mul]
    norm_num
  let f := coordinateSignMinusIsometry (normalWeights (2*n) d) (2*m) hk h2
    (fun i hi => normalWeights_initial (2*n) d i (by omega))
  let c := conjugateMinusIsometry R Q e.symm t
  let j := f.trans c
  have hminus := involutionMinusForm_nondegenerate Q g hQ hg
  have hsquares : (diagonalForm (fun _ : Fin (2*m) => (1 : F))).polarBilin.Nondegenerate :=
    isometry_between_nondegenerate _ _ j hminus
  refine ⟨g,hg,hdim,hdet,?_⟩
  rw [involution_wall_discriminantClass Q g hQ hg]
  exact (discriminantClass_isometry _ _ hsquares hminus j).symm.trans
    (discriminantClass_sum_squares (2*m) hsquares)
end Atlas.Quadratic
