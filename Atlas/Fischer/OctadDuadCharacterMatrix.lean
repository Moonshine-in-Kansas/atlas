import Atlas.Algebra.BinaryQuadraticTranslation
import Atlas.Fischer.OctadicCharacterPairings

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Orthogonality of the actual nondegenerate polar-character matrix. This
identity becomes the duad matrix identity after the Parker contraction bridge. -/
theorem binaryQuadratic_polar_sign_pair_sum (w : binaryQuadraticCode)
    (hr : binaryWalshPolarRank (binaryQuadraticWordForm w)=4) (s t : BinaryFour) :
    (∑ v : BinaryFour,
      parkerScalarSign ((binaryQuadraticWordForm w).polarBilin s v) *
      parkerScalarSign ((binaryQuadraticWordForm w).polarBilin t v)) =
      if s=t then (16 : Scalar) else 0 := by
  let B := (binaryQuadraticWordForm w).polarBilin
  have hp (v : BinaryFour) : parkerScalarSign (B s v)*parkerScalarSign (B t v)=
      parkerScalarSign ((B s+B t) v) := by
    rw [LinearMap.add_apply,parkerScalarSign_add]
  change (∑ v,parkerScalarSign (B s v)*parkerScalarSign (B t v))=_
  simp_rw [hp]
  have hs := parkerScalarSign_sum (B s+B t).toAddMonoidHom
  change (∑ v,parkerScalarSign ((B s+B t) v))=_ at hs
  have hz : (B s+B t).toAddMonoidHom=0 ↔ s=t := by
    constructor
    · intro h
      apply binaryQuadraticWordForm_polar_injective w hr
      apply LinearMap.ext
      intro v
      have he := DFunLike.congr_fun h v
      change B s v+B t v=0 at he
      exact (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _)
    · intro h
      subst t
      apply AddMonoidHom.ext
      intro v
      change B s v+B s v=0
      exact CharTwo.add_self_eq_zero _
  rw [hz] at hs
  have hc : Fintype.card BinaryFour=16 := by decide
  simpa [hc] using hs

end Atlas.Fischer
