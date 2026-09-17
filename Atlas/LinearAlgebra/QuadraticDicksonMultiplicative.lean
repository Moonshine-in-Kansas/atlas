import Atlas.LinearAlgebra.QuadraticDicksonReflection
import Atlas.LinearGroups.Orthogonal.ReflectionGroup

/-! # Residual parity on the actual reflection subgroup

Multiplicativity here requires membership in the reflection subgroup, rather than
an unproved global generation assertion in characteristic two.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

private abbrev parity (g : isometrySubgroup Q) : ZMod 2 :=
  dicksonParity Q (isometryCarrierEquiv Q g)

omit [FiniteDimensional F V] in
private theorem parity_one : parity Q 1 = 0 := by
  have hr : residual Q (isometryCarrierEquiv Q (1 : isometrySubgroup Q)) = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change y - y ∈ (⊥ : Submodule F V)
      simp
    · intro hx
      have hx' : x = 0 := (Submodule.mem_bot F).mp hx
      subst x
      exact ⟨0, map_zero _⟩
  unfold parity dicksonParity
  rw [hr, finrank_bot, Nat.cast_zero]

include hQ in
private theorem parity_reflection_mul (a : V) (ha : Q a ≠ 0)
    (g : isometrySubgroup Q) :
    parity Q (reflectionElement Q a ha * g) = 1 + parity Q g := by
  have hi : isometryCarrierEquiv Q (reflectionElement Q a ha * g) =
      reflectedIsometry Q (isometryCarrierEquiv Q g) a ha := by
    apply DFunLike.ext
    intro x
    rfl
  change dicksonParity Q (isometryCarrierEquiv Q (reflectionElement Q a ha * g)) = _
  rw [hi]
  exact (dicksonParity_reflection Q (isometryCarrierEquiv Q g) hQ a ha).trans
    (add_comm _ _)

include hQ in
private theorem parity_reflection (a : V) (ha : Q a ≠ 0) :
    parity Q (reflectionElement Q a ha) = 1 := by
  have h := parity_reflection_mul Q hQ a ha 1
  simpa only [mul_one, parity_one, add_zero] using h

include hQ in
/-- Intrinsic residual parity is additive when the left factor lies in the actual
reflection subgroup; the right factor is an arbitrary quadratic isometry. -/
theorem dicksonParity_mul_of_mem_reflectionSubgroup
    (g : isometrySubgroup Q) (hg : g ∈ reflectionSubgroup Q) (h : isometrySubgroup Q) :
    dicksonParity Q (isometryCarrierEquiv Q (g * h)) =
      dicksonParity Q (isometryCarrierEquiv Q g) +
      dicksonParity Q (isometryCarrierEquiv Q h) := by
  change parity Q (g * h) = parity Q g + parity Q h
  have hall : ∀ k : isometrySubgroup Q, k ∈ reflectionSubgroup Q →
      ∀ t, parity Q (k * t) = parity Q k + parity Q t := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨a, ha, rfl⟩ := hk
      intro t
      rw [parity_reflection_mul Q hQ, parity_reflection Q hQ]
    | one => intro t; simp only [one_mul, parity_one, zero_add]
    | mul x y hx hy ihx ihy =>
      intro t
      rw [mul_assoc, ihx, ihy, ihx, add_assoc]
    | inv x hx ih =>
      intro t
      apply add_left_cancel (a := parity Q x)
      rw [← ih, mul_inv_cancel_left, ← add_assoc, ← ih, mul_inv_cancel,
        parity_one, zero_add]
  exact hall g hg h

/-- The Dickson character on the actual reflection subgroup. Its value is defined
by residual rank, and is not obtained by choosing a reflection word. -/
def reflectionDicksonCharacter : reflectionSubgroup Q →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (dicksonParity Q (isometryCarrierEquiv Q g.val))
  map_one' := parity_one Q
  map_mul' g h := dicksonParity_mul_of_mem_reflectionSubgroup Q hQ g.val g.prop h.val

end Atlas.Orthogonal
