import Atlas.LinearAlgebra.BilinearDeterminantTransport
import Atlas.LinearAlgebra.InvolutionEigenspaceRestrictions
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Determinant square classes multiply across orthogonal direct decompositions -/
noncomputable section
namespace Atlas.Bilinear
variable {F V ι κ μ : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

theorem determinantClass_orthogonal_decomposition
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (P R : Submodule F V) (hc : IsCompl P R)
    (hpr : ∀ x : P, ∀ y : R, B x.val y.val = 0)
    (hrp : ∀ y : R, ∀ x : P, B y.val x.val = 0)
    (hP : (B.restrict P).Nondegenerate) (hR : (B.restrict R).Nondegenerate)
    (b : Module.Basis ι F V) (p : Module.Basis κ F P) (r : Module.Basis μ F R) :
    determinantClass B hB b =
      determinantClass (B.restrict P) hP p * determinantClass (B.restrict R) hR r := by
  let e := Submodule.prodEquivOfIsCompl P R hc
  let c := (p.prod r).map e
  rw [determinantClass_basis_independent_any B hB b c]
  have hm : LinearMap.BilinForm.toMatrix c B = Matrix.fromBlocks
      (LinearMap.BilinForm.toMatrix p (B.restrict P)) 0 0
      (LinearMap.BilinForm.toMatrix r (B.restrict R)) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    all_goals simp [c,e,LinearMap.BilinForm.toMatrix_apply,
      Module.Basis.map_apply,Module.Basis.prod_apply,
      LinearMap.inl_apply,LinearMap.inr_apply,hpr,hrp]
  unfold determinantClass
  rw [← map_mul]
  apply congrArg (Atlas.squareClass F)
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix c B).det =
    (LinearMap.BilinForm.toMatrix p (B.restrict P)).det *
      (LinearMap.BilinForm.toMatrix r (B.restrict R)).det
  rw [hm,Matrix.det_fromBlocks_zero₂₁]

/-- The actual plus/minus decomposition of an isometric involution gives the
product relation for arbitrary independently chosen bases of all three spaces. -/
theorem determinantClass_involution
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hpres : ∀ x y, B (t x) (t y) = B x y) (h2 : (2 : F) ≠ 0)
    (b : Module.Basis ι F V) (p : Module.Basis κ F (Atlas.LinearInvolution.plus t))
    (r : Module.Basis μ F (Atlas.LinearInvolution.minus t)) :
    determinantClass B hB b =
      determinantClass (B.restrict (Atlas.LinearInvolution.plus t))
        (Atlas.LinearInvolution.plus_nondegenerate B hB t ht hpres h2) p *
      determinantClass (B.restrict (Atlas.LinearInvolution.minus t))
        (Atlas.LinearInvolution.minus_nondegenerate B hB t ht hpres h2) r :=
  determinantClass_orthogonal_decomposition B hB _ _
    (Atlas.LinearInvolution.isCompl t ht h2)
    (Atlas.LinearInvolution.orthogonal B t hpres h2)
    (fun y x => Atlas.LinearInvolution.orthogonal B.flip t (fun x y => hpres y x) h2 x y)
    _ _ b p r
end Atlas.Bilinear
