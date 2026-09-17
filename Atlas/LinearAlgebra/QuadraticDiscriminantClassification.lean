import Atlas.LinearAlgebra.QuadraticDiagonalNormalization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Atlas.LinearAlgebra.QuadraticNondegenerateTransport

noncomputable section
namespace Atlas.Quadratic
variable {F : Type*} [Field F] [Invertible (2 : F)]

theorem diagonal_toMatrix {n : ℕ} (w : Fin n → F) :
    (diagonalForm w).toMatrix' = Matrix.diagonal w := by
  ext i j
  simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
    QuadraticMap.associated_apply, diagonalForm, QuadraticMap.weightedSumSquares_apply,
    Pi.add_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib]
    field_simp
    ring
  · simp [Matrix.diagonal_apply, h, Ne.symm h, Pi.single_apply,
      add_mul, mul_add, Finset.sum_add_distrib]

theorem diagonal_discr {n : ℕ} (w : Fin n → F) :
    (diagonalForm w).discr' = ∏ i, w i := by
  simp [QuadraticForm.discr', diagonal_toMatrix, Matrix.det_diagonal]

theorem discr_ratio_isSquare_of_isometry {n : ℕ}
    {Q R : QuadraticForm F (Fin n → F)} (e : Q.IsometryEquiv R)
    (hR : R.discr' ≠ 0) : IsSquare (Q.discr' / R.discr') := by
  have he : R.comp e.toLinearEquiv.toLinearMap = Q := by
    ext v
    exact e.map_app v
  have hd := QuadraticForm.discr'_comp (Q := R) e.toLinearEquiv.toLinearMap
  rw [he] at hd
  refine ⟨(LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det, ?_⟩
  rw [hd, mul_div_cancel_right₀ _ hR]

theorem finite_diagonal_isometry_iff_square_ratio [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w z : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) (hz : ∀ i, z i ≠ 0) :
    Nonempty ((diagonalForm w).IsometryEquiv (diagonalForm z)) ↔
      IsSquare ((∏ i, w i) / ∏ i, z i) := by
  constructor
  · rintro ⟨e⟩
    have hz0 : (diagonalForm z).discr' ≠ 0 := by
      rw [diagonal_discr]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
    simpa only [diagonal_discr] using discr_ratio_isSquare_of_isometry e hz0
  · exact finite_diagonal_isometry_of_square_ratio h2 n w z hw hz

theorem associated_separating_of_polar_nondegenerate {V : Type*}
    [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) : Q.associated.SeparatingLeft := by
  intro x hx
  apply hQ.1
  intro y
  have hp := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := F) Q)
  simp only [LinearMap.smul_apply, nsmul_eq_mul, hx, mul_zero] at hp
  exact hp.symm

theorem discr_ne_zero_of_nondegenerate {n : ℕ} (Q : QuadraticForm F (Fin n → F))
    (hQ : Q.polarBilin.Nondegenerate) : Q.discr' ≠ 0 := by
  have ha := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (associated_separating_of_polar_nondegenerate Q hQ)
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun F (Fin n))).mp ha

theorem finite_nondegenerate_diagonalization {n : ℕ}
    (Q : QuadraticForm F (Fin n → F)) (hQ : Q.polarBilin.Nondegenerate) :
    ∃ w : Fin n → F, (∀ i, w i ≠ 0) ∧ Nonempty (Q.IsometryEquiv (diagonalForm w)) := by
  have h : ∃ w : Fin n → Fˣ, Nonempty (Q.IsometryEquiv
      (QuadraticMap.weightedSumSquares F w)) := by
    have hh := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
      (associated_separating_of_polar_nondegenerate Q hQ)
    rw [Module.finrank_fin_fun] at hh
    exact hh
  obtain ⟨w, he⟩ := h
  refine ⟨fun i => (w i : F), fun i => (w i).ne_zero, ?_⟩
  simpa only [weighted_units_eq_diagonal] using he

theorem finite_nondegenerate_isometry_iff_discr_square [Finite F]
    (h2 : (2 : F) ≠ 0) (n : ℕ)
    (Q R : QuadraticForm F (Fin (n + 1) → F))
    (hQ : Q.polarBilin.Nondegenerate) (hR : R.polarBilin.Nondegenerate) :
    Nonempty (Q.IsometryEquiv R) ↔ IsSquare (Q.discr' / R.discr') := by
  have hQ0 := discr_ne_zero_of_nondegenerate Q hQ
  have hR0 := discr_ne_zero_of_nondegenerate R hR
  constructor
  · rintro ⟨e⟩
    exact discr_ratio_isSquare_of_isometry e hR0
  · intro hs
    obtain ⟨w, hw, ⟨e⟩⟩ := finite_nondegenerate_diagonalization Q hQ
    obtain ⟨z, hz, ⟨f⟩⟩ := finite_nondegenerate_diagonalization R hR
    have hw0 : (∏ i, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
    have hz0 : (∏ i, z i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
    have he : IsSquare ((∏ i, w i) / Q.discr') := by
      simpa only [diagonal_discr] using discr_ratio_isSquare_of_isometry e.symm hQ0
    have hf : IsSquare (R.discr' / ∏ i, z i) := by
      simpa only [diagonal_discr] using discr_ratio_isSquare_of_isometry f
        (show (diagonalForm z).discr' ≠ 0 by rwa [diagonal_discr])
    have heq : ((∏ i, w i) / Q.discr') * (Q.discr' / R.discr') *
        (R.discr' / ∏ i, z i) = (∏ i, w i) / ∏ i, z i := by
      field_simp
    have h := (he.mul hs).mul hf
    rw [heq] at h
    obtain ⟨g⟩ := finite_diagonal_isometry_of_square_ratio h2 n w z hw hz h
    exact ⟨e.trans (g.trans f.symm)⟩

theorem basisRepr_discr {V : Type*} [AddCommGroup V] [Module F V]
    {n : ℕ} (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) :
    QuadraticForm.discr' (Q.basisRepr b) = Q.discr b := by
  unfold QuadraticForm.discr' QuadraticForm.discr
  congr 1
  ext i j
  simp [QuadraticForm.toMatrix', QuadraticForm.toMatrix, QuadraticMap.basisRepr,
    QuadraticMap.associated_comp, LinearMap.toMatrix₂'_apply,
    LinearMap.toMatrix₂_apply]

theorem finite_nondegenerate_isometry_iff_basis_discr_square [Finite F]
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (h2 : (2 : F) ≠ 0) (n : ℕ)
    (Q : QuadraticForm F V) (R : QuadraticForm F W)
    (b : Module.Basis (Fin (n + 1)) F V) (c : Module.Basis (Fin (n + 1)) F W)
    (hQ : Q.polarBilin.Nondegenerate) (hR : R.polarBilin.Nondegenerate) :
    Nonempty (Q.IsometryEquiv R) ↔ IsSquare (Q.discr b / R.discr c) := by
  let e := Q.isometryEquivBasisRepr b
  let f := R.isometryEquivBasisRepr c
  have hq := isometry_between_nondegenerate _ _ e.symm hQ
  have hr := isometry_between_nondegenerate _ _ f.symm hR
  have hh := finite_nondegenerate_isometry_iff_discr_square h2 n
    (Q.basisRepr b) (R.basisRepr c) hq hr
  rw [basisRepr_discr, basisRepr_discr] at hh
  constructor
  · rintro ⟨g⟩
    exact hh.mp ⟨e.symm.trans (g.trans f)⟩
  · intro hs
    obtain ⟨g⟩ := hh.mpr hs
    exact ⟨e.trans (g.trans f.symm)⟩

end Atlas.Quadratic
