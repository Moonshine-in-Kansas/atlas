import Atlas.LinearAlgebra.QuadraticDiscriminantClassification
import Atlas.LinearAlgebra.BilinearDeterminantTransport

/-! # Quadratic classification using intrinsic determinant square classes -/
noncomputable section
namespace Atlas.Quadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
variable [Invertible (2 : F)]

theorem associated_nondegenerate (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) :
    Q.associated.Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (associated_separating_of_polar_nondegenerate Q hQ)

def discriminantClass (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) :
    Atlas.SquareClass F := Atlas.Bilinear.determinantClass Q.associated
      (associated_nondegenerate Q hQ) (Module.finBasis F V)

theorem discriminantClass_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (b : Module.Basis ι F V) :
    discriminantClass Q hQ = Atlas.Bilinear.determinantClass Q.associated
      (associated_nondegenerate Q hQ) b :=
  Atlas.Bilinear.determinantClass_basis_independent_any _ _ _ _

theorem square_ratio_of_squareClass_eq (u v : Fˣ)
    (h : Atlas.squareClass F u = Atlas.squareClass F v) : IsSquare ((u : F) / (v : F)) := by
  have hh : Atlas.squareClass F (u/v) = 1 := by rw [map_div,h,div_self']
  obtain ⟨w, hw⟩ := (Atlas.squareClass_eq_one F (u/v)).mp hh
  refine ⟨(w : F), ?_⟩
  have he := congrArg Units.val hw
  simpa only [Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,pow_two,Units.val_mul] using he.symm

/-- Equal dimension and intrinsic discriminant class give an actual isometry,
including the zero-dimensional case. -/
theorem finite_nondegenerate_isometry_of_discriminantClass [Finite F]
    (h2 : (2 : F) ≠ 0) (Q : QuadraticForm F V) (R : QuadraticForm F W)
    (hQ : Q.polarBilin.Nondegenerate) (hR : R.polarBilin.Nondegenerate)
    (hd : Module.finrank F V = Module.finrank F W)
    (hc : discriminantClass Q hQ = discriminantClass R hR) :
    Nonempty (Q.IsometryEquiv R) := by
  by_cases hz : Module.finrank F V = 0
  · have hz' : Module.finrank F W = 0 := hd.symm.trans hz
    haveI : Subsingleton V := (Module.finrank_zero_iff).mp hz
    haveI : Subsingleton W := (Module.finrank_zero_iff).mp hz'
    exact ⟨{ toLinearEquiv := LinearEquiv.ofSubsingleton V W
             map_app' := fun x => by simp [Subsingleton.elim x 0] }⟩
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
    let b := (Module.finBasis F V).reindex (finCongr hn)
    let c := (Module.finBasis F W).reindex (finCongr (hd.symm.trans hn))
    rw [discriminantClass_basis Q hQ b,discriminantClass_basis R hR c] at hc
    have hs := square_ratio_of_squareClass_eq
      (Atlas.Bilinear.gramUnit Q.associated (associated_nondegenerate Q hQ) b)
      (Atlas.Bilinear.gramUnit R.associated (associated_nondegenerate R hR) c) hc
    exact (finite_nondegenerate_isometry_iff_basis_discr_square h2 n Q R b c hQ hR).mpr hs

end Atlas.Quadratic
