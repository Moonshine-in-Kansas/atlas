import Atlas.Fischer.BinaryFourAffineCharacters
import Atlas.Fischer.MathieuOctadTranslations
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.Abelianization.Defs

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every binary character of the actual octad stabilizer kills its actual
pointwise translation kernel. -/
theorem mathieuOctad_character_pointwise (O : Octad)
    (f : MathieuOctadStabilizer O →* Multiplicative Bit)
    (g : MathieuOctadStabilizer O) (hg : g ∈ mathieuOctadPointwise O) : f g = 1 := by
  let e := mathieuOctadAffineEquivalence O
  let a := e g
  have hl : a.linear = 1 := by
    rw [← mathieuOctadTranslations_eq_pointwise] at hg
    exact hg
  have he : a = AffineEquiv.constVAdd Bit BinaryFourSpace (a 0) := by
    apply AffineEquiv.ext
    intro v
    have h := a.map_vadd (0 : BinaryFourSpace) v
    rw [hl] at h
    change a (v + 0) = v + a 0 at h
    simpa [AffineEquiv.constVAdd_apply, add_comm] using h
  have h := binaryFourAffine_character_translation (f.comp e.symm.toMonoidHom) (a 0)
  rw [← he] at h
  change f (e.symm (e g)) = 1 at h
  simpa only [MulEquiv.symm_apply_apply] using h

/-- The actual octad stabilizer has no nontrivial binary character. Its
translation kernel consists of affine commutators and its quotient is A8. -/
theorem mathieuOctad_character_trivial (O : Octad)
    (f : MathieuOctadStabilizer O →* Multiplicative Bit)
    (g : MathieuOctadStabilizer O) : f g = 1 := by
  let p := mathieuOctadAlternatingHom O
  have hp : p.range = ⊤ := MonoidHom.range_eq_top.mpr (mathieuOctadAlternating_surjective O)
  have hm : (commutator (MathieuOctadStabilizer O)).map p = ⊤ := by
    rw [map_commutator_eq, hp]
    exact commutator_alternatingGroup_eq_top (by rw [octadInterior_card]; decide)
  obtain ⟨k,hk,hkg⟩ := show p g ∈ (commutator (MathieuOctadStabilizer O)).map p from by
    rw [hm]; trivial
  have hf : f k = 1 := Abelianization.commutator_subset_ker f hk
  have hker : g*k⁻¹ ∈ mathieuOctadPointwise O := by
    change p (g*k⁻¹) = 1
    rw [map_mul, map_inv, hkg, mul_inv_cancel]
  have ht := mathieuOctad_character_pointwise O f (g*k⁻¹) hker
  simpa only [map_mul, map_inv, hf, inv_one, mul_one] using ht

end Atlas.Fischer
