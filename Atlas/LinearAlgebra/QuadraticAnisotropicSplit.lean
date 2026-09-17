import Atlas.LinearAlgebra.QuadraticHyperbolic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-! # Actual splitting off a nondegenerate quadratic line -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (a : V)

abbrev linePerp : Submodule F V := (Q.polarBilin.flip a).ker

def lineCoordinate : V →ₗ[F] F := (Q.polarBilin a a)⁻¹ • Q.polarBilin.flip a

variable (ha : Q.polarBilin a a ≠ 0)

include ha in
theorem lineCoordinate_self : lineCoordinate Q a a = 1 := inv_mul_cancel₀ ha

theorem lineCoordinate_perp (x : linePerp Q a) : lineCoordinate Q a x.val = 0 := by
  change (Q.polarBilin a a)⁻¹ * Q.polarBilin x.val a = 0
  have hx : Q.polarBilin x.val a = 0 := x.prop
  rw [hx, mul_zero]

include ha in
theorem lineRemainder_mem (x : V) : x - lineCoordinate Q a x • a ∈ linePerp Q a := by
  change Q.polarBilin (x-lineCoordinate Q a x • a) a = 0
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  change Q.polarBilin x a - ((Q.polarBilin a a)⁻¹ * Q.polarBilin x a) * Q.polarBilin a a = 0
  field_simp
  ring

def lineSplit : V ≃ₗ[F] F × linePerp Q a where
  toFun x := (lineCoordinate Q a x, ⟨x-lineCoordinate Q a x • a, lineRemainder_mem Q a ha x⟩)
  invFun x := x.1 • a + x.2.val
  left_inv x := by change lineCoordinate Q a x • a + (x-lineCoordinate Q a x • a) = x; abel
  right_inv x := by
    apply Prod.ext
    · change lineCoordinate Q a (x.1 • a + x.2.val) = x.1
      rw [map_add, map_smul, lineCoordinate_self Q a ha, lineCoordinate_perp, smul_eq_mul, mul_one, add_zero]
    · apply Subtype.ext
      change x.1 • a + x.2.val - lineCoordinate Q a (x.1 • a+x.2.val) • a = x.2.val
      rw [map_add, map_smul, lineCoordinate_self Q a ha, lineCoordinate_perp, smul_eq_mul, mul_one, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      change x+y-lineCoordinate Q a (x+y) • a = (x-lineCoordinate Q a x • a)+(y-lineCoordinate Q a y • a)
      rw [map_add, _root_.add_smul]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      change c • x-lineCoordinate Q a (c • x) • a = c • (x-lineCoordinate Q a x • a)
      rw [map_smul, smul_sub, smul_smul, smul_eq_mul]

include ha in
theorem linePerp_finrank [FiniteDimensional F V] : Module.finrank F (linePerp Q a) + 1 = Module.finrank F V := by
  have h := (lineSplit Q a ha).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm

def linePerpForm : QuadraticForm F (linePerp Q a) := Q.comp (linePerp Q a).subtype

@[simp] theorem linePerpForm_polar (x y : linePerp Q a) :
    (linePerpForm Q a).polarBilin x y = Q.polarBilin x.val y.val := by
  rw [linePerpForm, QuadraticMap.polarBilin_comp]
  rfl

include ha in
theorem lineSplit_form (x : F × linePerp Q a) :
    Q ((lineSplit Q a ha).symm x) = x.1^2 * Q a + Q x.2.val := by
  have hx : Q.polarBilin x.2.val a = 0 := x.2.prop
  have hax : Q.polarBilin a x.2.val = 0 := (polar_swap Q a x.2.val).trans hx
  change Q (x.1 • a + x.2.val) = _
  rw [QuadraticMap.map_add Q]
  change Q (x.1 • a) + Q x.2.val + Q.polarBilin (x.1 • a) x.2.val = _
  rw [Q.map_smul, map_smul, LinearMap.smul_apply, hax, smul_zero]
  simp only [smul_eq_mul, pow_two, add_zero]

include ha in
theorem linePerpForm_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    (linePerpForm Q a).polarBilin.Nondegenerate := by
  have hl : ∀ x : linePerp Q a, (∀ y, (linePerpForm Q a).polarBilin x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply hQ.1
    intro y
    let t := lineSplit Q a ha y
    have hy := (lineSplit Q a ha).symm_apply_apply y
    change t.1 • a + t.2.val = y at hy
    have hxa : Q.polarBilin x.val a = 0 := x.prop
    have hxt : Q.polarBilin x.val t.2.val = 0 := (linePerpForm_polar Q a x t.2).symm.trans (hx t.2)
    rw [← hy, map_add, map_smul, hxa, hxt, smul_zero, zero_add]
  constructor
  · exact hl
  · intro x hx
    apply hl x
    intro y
    rw [polar_swap]
    exact hx y

end Atlas.Quadratic
