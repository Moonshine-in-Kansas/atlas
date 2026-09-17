import Atlas.LinearAlgebra.QuadraticWallReflectionLaw
import Atlas.LinearGroups.Orthogonal.ReflectionGeneration

/-! # Intrinsic Wall spinor norm in odd characteristic -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

def wallClass (g : isometrySubgroup Q) : Atlas.SquareClass F :=
  wallDeterminantClass Q hQ (isometryCarrierEquiv Q g)

theorem wallClass_one : wallClass Q hQ 1 = 1 := by
  let g := isometryCarrierEquiv Q (1 : isometrySubgroup Q)
  have hr : residual Q g = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change y-y ∈ (⊥ : Submodule F V)
      simp
    · intro hx
      have hx' : x = 0 := (Submodule.mem_bot F).mp hx
      subst x
      exact ⟨0, map_zero _⟩
  have hd : Module.finrank F (residual Q g) = 0 := by rw [hr, finrank_bot]
  letI : IsEmpty (Fin (Module.finrank F (residual Q g))) := by rw [hd]; infer_instance
  have he : Atlas.Bilinear.gramUnit (wallForm Q g) (wallForm_nondegenerate Q g hQ)
      (Module.finBasis F (residual Q g)) = 1 := by
    apply Units.ext
    exact Matrix.det_isEmpty
  change Atlas.squareClass F _ = 1
  rw [he, map_one]

theorem wallClass_reflection_mul (a : V) (ha : Q a ≠ 0) (g : isometrySubgroup Q) :
    wallClass Q hQ (reflectionElement Q a ha * g) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) * wallClass Q hQ g :=
  wallDeterminantClass_reflection Q hQ (isometryCarrierEquiv Q g) a ha

theorem wallClass_reflection (a : V) (ha : Q a ≠ 0) :
    wallClass Q hQ (reflectionElement Q a ha) = Atlas.squareClass F (Units.mk0 (Q a) ha) := by
  have h := wallClass_reflection_mul Q hQ a ha 1
  simpa only [mul_one, wallClass_one] using h

/-- Wall's determinant class is multiplicative in odd characteristic. -/
theorem wallClass_mul (h2 : (2 : F) ≠ 0) (g h : isometrySubgroup Q) :
    wallClass Q hQ (g*h) = wallClass Q hQ g * wallClass Q hQ h := by
  have hg : g ∈ reflectionSubgroup Q := by rw [reflectionSubgroup_eq_top Q hQ h2]; trivial
  have hall : ∀ k : isometrySubgroup Q, k ∈ reflectionSubgroup Q →
      ∀ t, wallClass Q hQ (k*t) = wallClass Q hQ k * wallClass Q hQ t := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨a, ha, rfl⟩ := hk
      intro t
      rw [wallClass_reflection_mul, wallClass_reflection]
    | one => intro t; simp only [one_mul, wallClass_one]
    | mul x y hx hy ihx ihy =>
      intro t
      rw [mul_assoc, ihx, ihy, ihx, mul_assoc]
    | inv x hx ih =>
      intro t
      apply mul_left_cancel (a := wallClass Q hQ x)
      rw [← ih, mul_inv_cancel_left, ← mul_assoc, ← ih, mul_inv_cancel,
        wallClass_one, one_mul]
  exact hall g hg h

/-- The intrinsic spinor norm, defined by the determinant class of Wall's residual form. -/
def spinorNorm (h2 : (2 : F) ≠ 0) : isometrySubgroup Q →* Atlas.SquareClass F where
  toFun := wallClass Q hQ
  map_one' := wallClass_one Q hQ
  map_mul' := wallClass_mul Q hQ h2

@[simp] theorem spinorNorm_reflection (h2 : (2 : F) ≠ 0) (a : V) (ha : Q a ≠ 0) :
    spinorNorm Q hQ h2 (reflectionElement Q a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) := wallClass_reflection Q hQ a ha

end Atlas.Orthogonal

