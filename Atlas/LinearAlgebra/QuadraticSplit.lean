import Atlas.LinearAlgebra.QuadraticHyperbolic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Module

/-! # The explicit orthogonal splitting at a quadratic hyperbolic pair -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)

def complement : Submodule F V := (Q.polarBilin.flip e).ker ⊓ (Q.polarBilin.flip f).ker

@[simp] theorem mem_complement (x : V) :
    x ∈ complement Q e f ↔ Q.polarBilin x e = 0 ∧ Q.polarBilin x f = 0 := Iff.rfl

def planeProjection : V →ₗ[F] V :=
  (Q.polarBilin.flip f).smulRight e + (Q.polarBilin.flip e).smulRight f

@[simp] theorem planeProjection_apply (x : V) :
    planeProjection Q e f x = Q.polarBilin x f • e + Q.polarBilin x e • f := rfl

variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
theorem remainder_mem (x : V) : x - planeProjection Q e f x ∈ complement Q e f := by
  have hee : Q.polarBilin e e = 0 := by rw [polar_self,he,mul_zero]
  have hff : Q.polarBilin f f = 0 := by rw [polar_self,hf,mul_zero]
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  simp only [mem_complement,planeProjection_apply,map_sub,map_add,map_smul,
    LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    hee,hff,hef,hfe]
  constructor <;> ring

/-- Actual linear coordinates on the chosen plane and its perpendicular complement. -/
def split : V ≃ₗ[F] (F × F) × complement Q e f where
  toFun x := ((Q.polarBilin x f,Q.polarBilin x e),
    ⟨x-planeProjection Q e f x,remainder_mem Q e f he hf hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by simp only [planeProjection_apply]; module
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw := (mem_complement Q e f w).mp hw
    have hee : Q.polarBilin e e = 0 := by rw [polar_self,he,mul_zero]
    have hff : Q.polarBilin f f = 0 := by rw [polar_self,hf,mul_zero]
    have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
    apply Prod.ext
    · apply Prod.ext <;>
        simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
          smul_eq_mul,hee,hff,hef,hfe,hw.1,hw.2,mul_zero,mul_one,zero_add,add_zero]
    · apply Subtype.ext
      simp only [planeProjection_apply,map_add,map_smul,LinearMap.add_apply,
        LinearMap.smul_apply,smul_eq_mul,hee,hff,hef,hfe,hw.1,hw.2,
        mul_zero,mul_one,zero_add,add_zero]
      module
  map_add' x y := by
    apply Prod.ext
    · simp only [map_add,LinearMap.add_apply,Prod.mk_add_mk]
    · apply Subtype.ext
      change x+y-planeProjection Q e f (x+y) =
        (x-planeProjection Q e f x)+(y-planeProjection Q e f y)
      rw [map_add]
      module
  map_smul' a x := by
    apply Prod.ext
    · simp only [map_smul,LinearMap.smul_apply,Prod.smul_mk,RingHom.id_apply]
    · apply Subtype.ext
      change a • x-planeProjection Q e f (a • x) = a • (x-planeProjection Q e f x)
      rw [map_smul,smul_sub]

include he hf hef in
/-- Splitting off a hyperbolic pair drops the vector-space dimension by two. -/
theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement Q e f) + 2 = Module.finrank F V := by
  have h := (split Q e f he hf hef).finrank_eq
  simpa [Module.finrank_prod,Module.finrank_self,Nat.add_comm] using h.symm

/-- The splitting preserves the complete quadratic form, in arbitrary characteristic. -/
theorem split_form (t : (F × F) × complement Q e f) :
    Q ((split Q e f he hf hef).symm t) = t.1.1 * t.1.2 + Q t.2.val := by
  rcases t with ⟨⟨r,s⟩,⟨w,hw⟩⟩
  have hw := (mem_complement Q e f w).mp hw
  have hew : Q.polarBilin e w = 0 := (polar_swap Q e w).trans hw.1
  have hfw : Q.polarBilin f w = 0 := (polar_swap Q f w).trans hw.2
  change Q (r • e + s • f + w) = r*s + Q w
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q]
  change Q (r • e) + Q (s • f) + Q.polarBilin (r • e) (s • f) + Q w +
    Q.polarBilin (r • e + s • f) w = _
  simp only [Q.map_smul,map_smul,map_add,LinearMap.add_apply,LinearMap.smul_apply,
    smul_eq_mul,he,hf,hef,hew,hfw]
  ring

/-- Quadratic value in the coordinates of a chosen hyperbolic pair. -/
theorem form_split (x : V) :
    Q x = (split Q e f he hf hef x).1.1 * (split Q e f he hf hef x).1.2 +
      Q (split Q e f he hf hef x).2.val := by
  simpa only [LinearEquiv.symm_apply_apply] using
    split_form Q e f he hf hef (split Q e f he hf hef x)

end Atlas.Quadratic

