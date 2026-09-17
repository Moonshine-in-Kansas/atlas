import Atlas.LinearAlgebra.QuadraticInvolutionClass
import Atlas.LinearAlgebra.BilinearDeterminantProduct
import Atlas.LinearAlgebra.InvolutionConjugacy
noncomputable section
namespace Atlas.Quadratic
open Atlas.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V] [Invertible (2 : F)]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

theorem isometry_associated (x y : V) : Q.associated (g x) (g y) = Q.associated x y := by
  simp only [QuadraticMap.associated_apply]
  have he : g (x+y) = g x + g y := g.toLinearEquiv.map_add x y
  rw [← he,g.map_app,g.map_app,g.map_app]

theorem involution_discriminant_product (hQ : Q.polarBilin.Nondegenerate)
    (hg : Function.Involutive g) :
    discriminantClass Q hQ =
      discriminantClass (involutionPlusForm Q g) (involutionPlusForm_nondegenerate Q g hQ hg) *
      discriminantClass (involutionMinusForm Q g) (involutionMinusForm_nondegenerate Q g hQ hg) := by
  have hp : LinearMap.BilinForm.restrict Q.associated (plus g.toLinearEquiv.toLinearMap) =
      (involutionPlusForm Q g).associated := by
    ext x y
    rw [involutionPlusForm,QuadraticMap.associated_comp]
    rfl
  have hm : LinearMap.BilinForm.restrict Q.associated (minus g.toLinearEquiv.toLinearMap) =
      (involutionMinusForm Q g).associated := by
    ext x y
    rw [involutionMinusForm,QuadraticMap.associated_comp]
    rfl
  have hh := Atlas.Bilinear.determinantClass_involution Q.associated
    (associated_nondegenerate Q hQ) g.toLinearEquiv.toLinearMap hg (isometry_associated Q g)
    (Invertible.ne_zero (2 : F)) (Module.finBasis F V)
    (Module.finBasis F (plus g.toLinearEquiv.toLinearMap))
    (Module.finBasis F (minus g.toLinearEquiv.toLinearMap))
  apply hh.trans
  apply congrArg₂ (· * ·)
  · unfold discriminantClass Atlas.Bilinear.determinantClass
    apply congrArg (Atlas.squareClass F)
    apply Units.ext
    change (LinearMap.BilinForm.toMatrix _
      (LinearMap.BilinForm.restrict Q.associated (plus g.toLinearEquiv.toLinearMap))).det = _
    rw [hp]
    rfl
  · unfold discriminantClass Atlas.Bilinear.determinantClass
    apply congrArg (Atlas.squareClass F)
    apply Units.ext
    change (LinearMap.BilinForm.toMatrix _
      (LinearMap.BilinForm.restrict Q.associated (minus g.toLinearEquiv.toLinearMap))).det = _
    rw [hm]
    rfl

theorem involution_decomposition_quadratic (hg : Function.Involutive g)
    (x : plus g.toLinearEquiv.toLinearMap × minus g.toLinearEquiv.toLinearMap) :
    Q (decomposition g.toLinearEquiv.toLinearMap hg (Invertible.ne_zero (2 : F)) x) =
      Q x.1.val + Q x.2.val := by
  have h := orthogonal Q.polarBilin g.toLinearEquiv.toLinearMap
    (isometry_polar Q g) (Invertible.ne_zero (2 : F)) x.1 x.2
  change Q (x.1.val+x.2.val) = _
  change Q (x.1.val+x.2.val) - Q x.1.val - Q x.2.val = 0 at h
  linear_combination h

def involutionIsometryOfParts (s : Q.IsometryEquiv Q)
    (hg : Function.Involutive g) (hs : Function.Involutive s)
    (ep : (involutionPlusForm Q g).IsometryEquiv (involutionPlusForm Q s))
    (em : (involutionMinusForm Q g).IsometryEquiv (involutionMinusForm Q s)) :
    Q.IsometryEquiv Q where
  toLinearEquiv := conjugator g.toLinearEquiv.toLinearMap s.toLinearEquiv.toLinearMap
    hg hs (Invertible.ne_zero (2 : F)) ep.toLinearEquiv em.toLinearEquiv
  map_app' x := by
    obtain ⟨u,rfl⟩ := (decomposition g.toLinearEquiv.toLinearMap hg
      (Invertible.ne_zero (2 : F))).surjective x
    change Q (conjugator g.toLinearEquiv.toLinearMap s.toLinearEquiv.toLinearMap
      hg hs (Invertible.ne_zero (2 : F)) ep.toLinearEquiv em.toLinearEquiv
      (decomposition g.toLinearEquiv.toLinearMap hg (Invertible.ne_zero (2 : F)) u)) = _
    rw [conjugator_decomposition,involution_decomposition_quadratic,
      involution_decomposition_quadratic]
    exact congrArg₂ (· + ·) (ep.map_app u.1) (em.map_app u.2)

theorem involutionIsometryOfParts_intertwines (s : Q.IsometryEquiv Q)
    (hg : Function.Involutive g) (hs : Function.Involutive s)
    (ep : (involutionPlusForm Q g).IsometryEquiv (involutionPlusForm Q s))
    (em : (involutionMinusForm Q g).IsometryEquiv (involutionMinusForm Q s)) (x : V) :
    involutionIsometryOfParts Q g s hg hs ep em (g x) =
      s (involutionIsometryOfParts Q g s hg hs ep em x) :=
  conjugator_intertwines _ _ hg hs (Invertible.ne_zero (2 : F)) _ _ x

/-- In odd finite characteristic, dimension and intrinsic Wall class determine
ambient orthogonal conjugacy of actual involutions. -/
theorem involution_conjugator_of_wallClass [Finite F] (hQ : Q.polarBilin.Nondegenerate)
    (s : Q.IsometryEquiv Q) (hg : Function.Involutive g) (hs : Function.Involutive s)
    (hd : Module.finrank F (minus g.toLinearEquiv.toLinearMap) =
      Module.finrank F (minus s.toLinearEquiv.toLinearMap))
    (hc : wallDeterminantClass Q hQ g = wallDeterminantClass Q hQ s) :
    ∃ k : Q.IsometryEquiv Q, ∀ x : V, k (g x) = s (k x) := by
  have h2 := Invertible.ne_zero (2 : F)
  have hm : discriminantClass (involutionMinusForm Q g)
      (involutionMinusForm_nondegenerate Q g hQ hg) =
      discriminantClass (involutionMinusForm Q s)
      (involutionMinusForm_nondegenerate Q s hQ hs) := by
    rwa [involution_wall_discriminantClass Q g hQ hg,
      involution_wall_discriminantClass Q s hQ hs] at hc
  have hp : discriminantClass (involutionPlusForm Q g)
      (involutionPlusForm_nondegenerate Q g hQ hg) =
      discriminantClass (involutionPlusForm Q s)
      (involutionPlusForm_nondegenerate Q s hQ hs) := by
    have h := (involution_discriminant_product Q g hQ hg).symm.trans
      (involution_discriminant_product Q s hQ hs)
    rw [hm] at h
    exact mul_right_cancel h
  have hdp : Module.finrank F (plus g.toLinearEquiv.toLinearMap) =
      Module.finrank F (plus s.toLinearEquiv.toLinearMap) := by
    have hgdim := finrank_plus_add_minus g.toLinearEquiv.toLinearMap hg h2
    have hsdim := finrank_plus_add_minus s.toLinearEquiv.toLinearMap hs h2
    omega
  obtain ⟨ep⟩ := finite_nondegenerate_isometry_of_discriminantClass h2
    (involutionPlusForm Q g) (involutionPlusForm Q s)
    (involutionPlusForm_nondegenerate Q g hQ hg) (involutionPlusForm_nondegenerate Q s hQ hs) hdp hp
  obtain ⟨em⟩ := finite_nondegenerate_isometry_of_discriminantClass h2
    (involutionMinusForm Q g) (involutionMinusForm Q s)
    (involutionMinusForm_nondegenerate Q g hQ hg) (involutionMinusForm_nondegenerate Q s hQ hs) hd hm
  exact ⟨involutionIsometryOfParts Q g s hg hs ep em,
    involutionIsometryOfParts_intertwines Q g s hg hs ep em⟩

end Atlas.Quadratic
