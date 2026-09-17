import Atlas.Fischer.BinaryFourAffineOrder
import Mathlib.LinearAlgebra.Pi

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

def binaryFourBasis (i : Fin 4) : BinaryFourSpace := Pi.single i 1

/-- A coordinate shear on the actual four-dimensional binary affine space. -/
def binaryFourShear (i j : Fin 4) (hij : i ≠ j) :
    BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace :=
  LinearEquiv.ofInvolutive
    (LinearMap.id + (LinearMap.proj j).smulRight (binaryFourBasis i)) (by
      intro v
      change v + v j • binaryFourBasis i +
        (v + v j • binaryFourBasis i) j • binaryFourBasis i = v
      ext k
      by_cases hk : k = i
      · subst k
        simp [binaryFourBasis, Pi.single_apply, hij, Ne.symm hij, add_smul, add_assoc, CharTwo.add_self_eq_zero]
      · simp [binaryFourBasis, Pi.single_apply, hk, Ne.symm hk])

/-- Any binary character of the full affine group kills every translation.
Coordinate shears conjugate a basis translation to its product with another. -/
theorem binaryFourAffine_character_translation
    (f : (BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace) →* Multiplicative Bit)
    (v : BinaryFourSpace) : f (AffineEquiv.constVAdd Bit BinaryFourSpace v) = 1 := by
  classical
  let l : BinaryFourSpace →+ Bit := {
    toFun := fun v => (f (AffineEquiv.constVAdd Bit BinaryFourSpace v)).toAdd
    map_zero' := by
      rw [AffineEquiv.constVAdd_zero]
      change (f 1).toAdd = 0
      rw [map_one]
      rfl
    map_add' := by
      intro v w
      exact congrArg Multiplicative.toAdd
        ((f.comp (AffineEquiv.constVAddHom Bit BinaryFourSpace)).map_mul
          (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  have hb (i : Fin 4) : l (binaryFourBasis i) = 0 := by
    obtain ⟨j, hji⟩ := exists_ne i
    let L := (binaryFourShear i j (Ne.symm hji)).toAffineEquiv
    let T := AffineEquiv.constVAdd Bit BinaryFourSpace
    have he : L * T (binaryFourBasis j) = T (binaryFourBasis i + binaryFourBasis j) * L := by
      ext w k
      change (binaryFourBasis j + w) k +
        (binaryFourBasis j + w) j * binaryFourBasis i k =
          (binaryFourBasis i + binaryFourBasis j) k +
            (w k + w j * binaryFourBasis i k)
      simp only [binaryFourBasis, Pi.add_apply, Pi.single_eq_same]
      ring
    have hf := congrArg f he
    rw [map_mul, map_mul, mul_comm (f L)] at hf
    have ht := mul_right_cancel hf
    have hh : l (binaryFourBasis j) = l (binaryFourBasis i + binaryFourBasis j) :=
      congrArg Multiplicative.toAdd ht
    rw [map_add] at hh
    exact add_right_cancel (hh.symm.trans (zero_add _).symm)
  have hv : v = ∑ i : Fin 4, Pi.single i (v i) := by
    ext i
    simp
  have hz : l v = 0 := by
    rw [hv, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hbit : v i = 0 ∨ v i = 1 := by
      have h : ∀ a : Bit, a = 0 ∨ a = 1 := by decide
      exact h _
    rcases hbit with h | h
    · simp [h]
    · simpa only [h, binaryFourBasis] using hb i
  exact Multiplicative.toAdd.injective hz

end Atlas.Fischer
