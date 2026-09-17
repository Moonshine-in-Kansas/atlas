import Atlas.Fischer.OctadDuadBasis
import Atlas.Fischer.OctadDuadCharacterMatrix
import Atlas.Fischer.RootMapSubspaces

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem octadDuadSignedFamily_orthonormal {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hd : (support d.val.1.val ∩ O.val).card=2) (s t : BinaryFour) :
    hermitian (octadDuadSignedFamily Q d s) (octadDuadSignedFamily Q d t)=
      if s=t then 1 else 0 := by
  by_cases h : s=t
  · subst t
    rw [if_pos rfl]
    exact signedOctadVector_norm _
  · have hn : signedOctadSupport (octadTranslatedSignedOctad Q d s) ≠
        signedOctadSupport (octadTranslatedSignedOctad Q d t) := by
      intro he
      have hc := congrArg octadWord he
      simp only [octadWord_signedSupport,octadTranslatedSignedOctad_code] at hc
      exact h (octadTranslatedWord_duad_injective O d.val.1 hd hc)
    simp only [octadDuadSignedFamily,signedOctadVector,hermitian_smul_left,
      hermitian_smul_right,hermitian_xOctad,ite_eq_right hn,ite_eq_right h,mul_zero]

/-- The candidate row is specified by the actual polar form and actual signed basis. -/
def octadDuadCharacterRow {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (s : BinaryFour) : Coordinates :=
  (1 / 4 : Scalar) • ∑ t : BinaryFour,
    parkerScalarSign ((binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s t) •
      octadDuadSignedFamily Q d t

/-- Exact Hermitian identity for these rows; identifying the root map with them
is a separate actual product-table obligation. -/
theorem octadDuadCharacterRow_orthonormal {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hd : (support d.val.1.val ∩ O.val).card=2) (s t : BinaryFour) :
    hermitian (octadDuadCharacterRow Q d s) (octadDuadCharacterRow Q d t)=
      if s=t then 1 else 0 := by
  let B := (binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin
  have hp := binaryQuadratic_polar_sign_pair_sum (octadQuadraticRestriction O d.val.1)
    (octadQuadraticWord_rank_duad O d.val.1 hd) s t
  have hs : hermitian
      (∑ u : BinaryFour,parkerScalarSign (B s u) • octadDuadSignedFamily Q d u)
      (∑ v : BinaryFour,parkerScalarSign (B t v) • octadDuadSignedFamily Q d v)=
      if s=t then (16 : Scalar) else 0 := by
    rw [hermitian_sum_left]
    simp only [hermitian_sum_right,hermitian_smul_left,hermitian_smul_right,
      parkerScalarSign_star,octadDuadSignedFamily_orthonormal Q d hd,
      mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    change (∑ x,parkerScalarSign (B s x)*parkerScalarSign (B t x))=_ at hp
    calc
      _ = ∑ x,parkerScalarSign (B s x)*parkerScalarSign (B t x) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = _ := hp
  change hermitian ((1/4 : Scalar) • _ ) ((1/4 : Scalar) • _)=_
  rw [hermitian_smul_left,hermitian_smul_right,hs]
  split_ifs <;> norm_num

end Atlas.Fischer
