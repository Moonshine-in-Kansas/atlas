import Atlas.LinearGroups.SuzukiFamily.ProjectiveAction
import Atlas.LinearGroups.SuzukiFamily.RootSubgroup
import Atlas.LinearGroups.SuzukiFamily.BruhatRewrite

/-! Matrix relations lifted to the retained symplectic group, without a new carrier. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem matrix_injective : Function.Injective (matrix (F := F)) := by
  intro g h he
  exact Subtype.ext (toStandard.symm.injective he)

@[simp] theorem torusElement_one (m : ℕ) : torusElement m (1 : Fˣ)=1 := by
  apply matrix_injective
  simp

theorem torusElement_mul (m : ℕ) (s t : Fˣ) :
    torusElement m (s*t)=torusElement m s * torusElement m t := by
  apply matrix_injective
  simp [h_mul]

def torusHom (m : ℕ) : Fˣ →* Atlas.Symplectic.Sp 2 F where
  toFun := torusElement m
  map_one' := torusElement_one m
  map_mul' := torusElement_mul m

@[simp] theorem torusElement_inv (m : ℕ) (t : Fˣ) :
    torusElement m t⁻¹=(torusElement m t)⁻¹ := (torusHom m).map_inv t

theorem torusElement_injective (m : ℕ) : Function.Injective (torusElement (F := F) m) := by
  intro s t he
  exact h_injective m (by simpa using congrArg matrix he)

@[simp] theorem weylElement_square :
    (weylElement : Atlas.Symplectic.Sp 2 F)*weylElement=1 := by
  apply matrix_injective
  simp [w_square]

@[simp] theorem weylElement_inv : (weylElement : Atlas.Symplectic.Sp 2 F)⁻¹=weylElement :=
  inv_eq_of_mul_eq_one_right weylElement_square

theorem torus_root_conjugate (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (a b : F) :
    torusElement m t⁻¹ * rootElement m a b * torusElement m t =
      rootElement m (theta F m (t:F)*a) ((t:F)^2*theta F m (t:F)*b) := by
  apply matrix_injective
  simpa only [matrix_mul,matrix_torus,matrix_root] using h_conjugate_u m hcard t a b

theorem weyl_torus_weyl (m : ℕ) (t : Fˣ) :
    weylElement * torusElement m t * weylElement=torusElement m t⁻¹ := by
  apply matrix_injective
  simpa only [matrix_mul,matrix_torus,matrix_weyl] using w_h_w m t

theorem weyl_root_rewrite (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (hn : norm m a b ≠0) :
    weylElement * rootElement m a b * weylElement =
      rootElement m (inverseFirst m a b) (inverseSecond m a b) * weylElement *
        torusElement m (bruhatTorus m a b hn) *
        rootElement m (b/norm m a b) (a/norm m a b) := by
  apply matrix_injective
  simpa only [matrix_mul,matrix_root,matrix_torus,matrix_weyl] using
    weyl_root_weyl m hcard a b hn
end Atlas.SuzukiFamily
