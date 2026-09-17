import Atlas.LinearAlgebra.QuadraticComplementTransport

/-! # Extend complement isometries by the identity on a hyperbolic plane -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

def complementExtensionLinear
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) : V ≃ₗ[F] V :=
  (split Q e f he hf hef).trans
    (((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv).trans
      (split Q e f he hf hef).symm)

theorem complementExtension_preserves
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) (x : V) :
    Q (complementExtensionLinear Q e f he hf hef k x) = Q x := by
  change Q ((split Q e f he hf hef).symm
    ((split Q e f he hf hef x).1, k (split Q e f he hf hef x).2)) = Q x
  rw [split_form, form_split Q e f he hf hef x]
  have hk := k.map_app (split Q e f he hf hef x).2
  change Q (k (split Q e f he hf hef x).2).val = Q (split Q e f he hf hef x).2.val at hk
  exact congrArg (_ + ·) hk

/-- Extension uses the actual quadratic direct sum, with no dimension-only identification. -/
def complementExtension
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) : Q.IsometryEquiv Q where
  __ := complementExtensionLinear Q e f he hf hef k
  map_app' := complementExtension_preserves Q e f he hf hef k

include he hf hef in
theorem split_e : split Q e f he hf hef e = ((1, 0), 0) := by
  have hee : Q.polarBilin e e = 0 := by rw [polar_self, he, mul_zero]
  apply Prod.ext
  · exact Prod.ext hef hee
  · apply Subtype.ext
    change e - (Q.polarBilin e f • e + Q.polarBilin e e • f) = 0
    rw [hef, hee, one_smul, zero_smul, add_zero, sub_self]

include he hf hef in
theorem split_f : split Q e f he hf hef f = ((0, 1), 0) := by
  have hff : Q.polarBilin f f = 0 := by rw [polar_self, hf, mul_zero]
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  apply Prod.ext
  · exact Prod.ext hff hfe
  · apply Subtype.ext
    change f - (Q.polarBilin f f • e + Q.polarBilin f e • f) = 0
    rw [hff, hfe, zero_smul, one_smul, zero_add, sub_self]

include he hf hef in
theorem split_complement (x : complement Q e f) :
    split Q e f he hf hef x.val = ((0, 0), x) := by
  apply Prod.ext
  · exact Prod.ext x.prop.2 x.prop.1
  · apply Subtype.ext
    change x.val - (Q.polarBilin x.val f • e + Q.polarBilin x.val e • f) = x.val
    have hx := (mem_complement Q e f x.val).mp x.prop
    rw [hx.1, hx.2, zero_smul, zero_smul, add_zero, sub_zero]

theorem complementExtension_fix_e
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) :
    complementExtension Q e f he hf hef k e = e := by
  change (split Q e f he hf hef).symm
    ((split Q e f he hf hef e).1, k (split Q e f he hf hef e).2) = e
  rw [split_e]
  simp only [map_zero]
  change (1 : F) • e + (0 : F) • f + (0 : V) = e
  simp

theorem complementExtension_fix_f
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) :
    complementExtension Q e f he hf hef k f = f := by
  change (split Q e f he hf hef).symm
    ((split Q e f he hf hef f).1, k (split Q e f he hf hef f).2) = f
  rw [split_f]
  simp only [map_zero]
  change (0 : F) • e + (1 : F) • f + (0 : V) = f
  simp

theorem complementExtension_apply
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f))
    (x : complement Q e f) : complementExtension Q e f he hf hef k x.val = (k x).val := by
  change (split Q e f he hf hef).symm
    ((split Q e f he hf hef x.val).1, k (split Q e f he hf hef x.val).2) = (k x).val
  rw [split_complement]
  change (0 : F) • e + (0 : F) • f + (k x).val = (k x).val
  simp

end Atlas.Quadratic
