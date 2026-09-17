import Atlas.Fischer.OctadicCharacterPairings
import Atlas.Fischer.OctadCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
local instance octadicAverageCharacterFinite (O : Octad) : Finite (OctadicCharacter O) := Nat.finite_of_card_ne_zero (by rw [octadCharacters_card]; decide)
local instance octadicAverageCharacterFintype (O : Octad) : Fintype (OctadicCharacter O) := Fintype.ofFinite _

/-- Exact dual-character cancellation on a nonzero shortened Golay word. -/
theorem octadicCharacter_sign_sum (O : Octad) (b : octadShortenedCode O) (hb : b ≠ 0) :
    (∑ χ : OctadicCharacter O, parkerScalarSign (χ b)) = 0 := by
  classical
  let ev : OctadicCharacter O →+ Bit :=
    { toFun := fun χ => χ b
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : ev ≠ 0 := by
    intro h
    apply hb
    apply (Module.forall_dual_apply_eq_zero_iff Bit b).mp
    intro χ
    exact congrArg (fun f : OctadicCharacter O →+ Bit => f χ) h
  change (∑ χ, parkerScalarSign (ev χ)) = 0
  rw [parkerScalarSign_sum, if_neg he]

/-- Averaging the literal octadic formula cancels every signed octad term. -/
theorem octadicRoot_character_sum {O : Octad} (Q : OctadCalibration O) :
    (∑ χ : OctadicCharacter O, octadicRoot Q χ) = (16 : Scalar) • octadicAxisPart O := by
  classical
  have hc : Fintype.card (OctadicCharacter O) = 32 := by
    rw [← Nat.card_eq_fintype_card]
    exact octadCharacters_card O
  simp only [octadicRoot, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Finset.mul_sum,
    octadicCharacter_sign_sum O _ (octadShortenedOne_ne_zero O), mul_zero, zero_smul]
  have hh : ∀ b : OctadShortenedHyperplane O,
      (∑ χ : OctadicCharacter O, parkerScalarSign (χ b.val)) = 0 :=
    fun b => octadicCharacter_sign_sum O b.val b.property.1
  simp only [hh, zero_smul, Finset.sum_const_zero, add_zero,
    Finset.sum_const, Finset.card_univ, hc]
  rw [← Nat.cast_smul_eq_nsmul Scalar, smul_smul]
  norm_num

end Atlas.Fischer
