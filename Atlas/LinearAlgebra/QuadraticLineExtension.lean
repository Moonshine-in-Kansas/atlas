import Atlas.LinearAlgebra.QuadraticAnisotropicSplit
import Atlas.LinearAlgebra.QuadraticSiegel
import Atlas.LinearAlgebra.QuadraticReflection

/-! # Extend and restrict actual isometries at a nondegenerate quadratic line -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (a : V) (ha : Q.polarBilin a a ≠ 0)

def lineExtensionLinear (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) : V ≃ₗ[F] V :=
  (lineSplit Q a ha).trans (((LinearEquiv.refl F F).prodCongr k.toLinearEquiv).trans
    (lineSplit Q a ha).symm)

theorem lineExtension_preserves (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) (x : V) :
    Q (lineExtensionLinear Q a ha k x) = Q x := by
  change Q ((lineSplit Q a ha).symm ((lineSplit Q a ha x).1, k (lineSplit Q a ha x).2)) = Q x
  rw [lineSplit_form]
  have h := lineSplit_form Q a ha (lineSplit Q a ha x)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  have hk := k.map_app (lineSplit Q a ha x).2
  exact congrArg (_ + ·) hk

def lineExtension (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) : Q.IsometryEquiv Q where
  __ := lineExtensionLinear Q a ha k
  map_app' := lineExtension_preserves Q a ha k

include ha in
theorem lineSplit_self : lineSplit Q a ha a = (1, 0) := by
  apply Prod.ext
  · exact lineCoordinate_self Q a ha
  · apply Subtype.ext
    change a - lineCoordinate Q a a • a = 0
    rw [lineCoordinate_self Q a ha, one_smul, sub_self]

include ha in
theorem lineSplit_perp (x : linePerp Q a) : lineSplit Q a ha x.val = (0, x) := by
  apply Prod.ext
  · exact lineCoordinate_perp Q a x
  · apply Subtype.ext
    change x.val - lineCoordinate Q a x.val • a = x.val
    rw [lineCoordinate_perp, zero_smul, sub_zero]

theorem lineExtension_fix (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) :
    lineExtension Q a ha k a = a := by
  change (lineSplit Q a ha).symm ((lineSplit Q a ha a).1, k (lineSplit Q a ha a).2) = a
  rw [lineSplit_self]
  simp only [map_zero]
  change (1 : F) • a + (0 : V) = a
  simp

theorem lineExtension_apply (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a))
    (x : linePerp Q a) : lineExtension Q a ha k x.val = (k x).val := by
  change (lineSplit Q a ha).symm ((lineSplit Q a ha x.val).1, k (lineSplit Q a ha x.val).2) = (k x).val
  rw [lineSplit_perp]
  change (0 : F) • a + (k x).val = (k x).val
  simp

include ha in
theorem linear_ext_linePerp (g h : V →ₗ[F] V) (he : g a = h a)
    (hw : ∀ x : linePerp Q a, g x.val = h x.val) : g = h := by
  apply LinearMap.ext
  intro x
  have hx := (lineSplit Q a ha).symm_apply_apply x
  change (lineSplit Q a ha x).1 • a + (lineSplit Q a ha x).2.val = x at hx
  calc
    g x = g ((lineSplit Q a ha x).1 • a + (lineSplit Q a ha x).2.val) := congrArg g hx.symm
    _ = h ((lineSplit Q a ha x).1 • a + (lineSplit Q a ha x).2.val) := by rw [map_add, map_add, map_smul, map_smul, he, hw]
    _ = h x := congrArg h hx

def lineRestriction (g : Q.IsometryEquiv Q) (hg : g a = a) :
    (linePerpForm Q a).IsometryEquiv (linePerpForm Q a) where
  toFun x := ⟨g x.val, by
    change Q.polarBilin (g x.val) a = 0
    have h := isometry_polar Q g x.val a
    rw [hg] at h
    exact h.trans x.prop⟩
  invFun x := ⟨g.symm x.val, by
    change Q.polarBilin (g.symm x.val) a = 0
    have hga : g.symm a = a := by rw [← hg, g.symm_apply_apply]; exact hg.symm
    have h := isometry_polar Q g.symm x.val a
    rw [hga] at h
    exact h.trans x.prop⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add g x.val y.val)
  map_smul' c x := Subtype.ext (map_smul g c x.val)
  map_app' x := g.map_app x.val

theorem lineExtension_restriction (g : Q.IsometryEquiv Q) (hg : g a = a) :
    lineExtension Q a ha (lineRestriction Q a g hg) = g := by
  apply DFunLike.ext
  intro x
  have h := linear_ext_linePerp Q a ha
    (lineExtension Q a ha (lineRestriction Q a g hg)).toLinearEquiv.toLinearMap g.toLinearEquiv.toLinearMap
    ((lineExtension_fix Q a ha _).trans hg.symm)
    (fun w => lineExtension_apply Q a ha _ w)
  exact LinearMap.congr_fun h x


/-- A reflection in the perpendicular space extends to that same ambient reflection. -/
theorem lineExtension_reflection (u : linePerp Q a) (hu : Q u.val ≠ 0) :
    lineExtension Q a ha (reflectionIsometry (linePerpForm Q a) u hu) =
      reflectionIsometry Q u.val hu := by
  have hfix : reflectionIsometry Q u.val hu a = a := by
    change reflectionLinear Q u.val hu a = a
    rw [reflectionLinear_apply, polar_swap Q a u.val]
    have hp : Q.polarBilin u.val a = 0 := u.prop
    rw [hp, mul_zero, zero_smul, sub_zero]
  have hp : ∀ w : linePerp Q a,
      lineExtension Q a ha (reflectionIsometry (linePerpForm Q a) u hu) w.val =
        reflectionIsometry Q u.val hu w.val := by
    intro w
    rw [lineExtension_apply]
    change ((reflectionLinear (linePerpForm Q a) u hu w) : linePerp Q a).val =
      reflectionLinear Q u.val hu w.val
    rw [reflectionLinear_apply (linePerpForm Q a) u hu w, reflectionLinear_apply Q u.val hu w.val]
    change w.val - (((linePerpForm Q a) u)⁻¹ * (linePerpForm Q a).polarBilin w u) • u.val = _
    rw [linePerpForm_polar]
    rfl
  apply DFunLike.ext
  intro x
  exact LinearMap.congr_fun (linear_ext_linePerp Q a ha _ _
    ((lineExtension_fix Q a ha _).trans hfix.symm) hp) x

end Atlas.Quadratic
