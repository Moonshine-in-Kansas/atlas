import Atlas.Fischer.OctadDuadBlockPackage
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual full-rank duad polar form identifies the four-dimensional
translation space with its full binary dual. -/
def octadDuadPolarEquiv (O : Octad) (c : golay)
    (hc : (support c.val ∩ O.val).card=2) :
    BinaryFour ≃ₗ[Bit] Module.Dual Bit BinaryFour :=
  LinearEquiv.ofBijective (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin
    ⟨binaryQuadraticWordForm_polar_injective _ (octadQuadraticWord_rank_duad O c hc),
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp
        (binaryQuadraticWordForm_polar_injective _ (octadQuadraticWord_rank_duad O c hc))⟩

@[simp] theorem octadDuadPolarEquiv_apply (O : Octad) (c : golay)
    (hc : (support c.val ∩ O.val).card=2) (s t : BinaryFour) :
    octadDuadPolarEquiv O c hc s t=
      (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin s t := rfl

theorem octadDuadPolarEquiv_symm_apply (O : Octad) (c : golay)
    (hc : (support c.val ∩ O.val).card=2) (χ : Module.Dual Bit BinaryFour) (t : BinaryFour) :
    (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin
      ((octadDuadPolarEquiv O c hc).symm χ) t=χ t := by
  exact LinearMap.congr_fun ((octadDuadPolarEquiv O c hc).apply_symm_apply χ) t

/-- The canonical Walsh matrix: rows are all actual binary linear characters,
columns are the sixteen actual binary vectors. -/
def binaryFourWalshEntry (χ : Module.Dual Bit BinaryFour) (t : BinaryFour) : Scalar :=
  parkerScalarSign (χ t)

/-- Literal canonical Walsh coordinates for the actual duad root map. The row
index is transported by the proved polar equivalence, with no assumed gauge. -/
theorem rootMap_octadic_duad_canonicalWalsh {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hd : (support d.val.1.val ∩ O.val).card=2)
    (χ : Module.Dual Bit BinaryFour) :
    rootMap (octadicRoot Q 0)
      (octadDuadSignedFamily Q d ((octadDuadPolarEquiv O d.val.1 hd).symm χ))=
      (1/4 : Scalar) • ∑ t : BinaryFour,binaryFourWalshEntry χ t • octadDuadSignedFamily Q d t := by
  rw [rootMap_octadic_duad_row Q d hd]
  unfold octadDuadCharacterRow
  simp only [octadDuadPolarEquiv_symm_apply,binaryFourWalshEntry]

/-- The canonical Walsh matrix has the exact Hadamard row identity. -/
theorem binaryFourWalshEntry_pair_sum (O : Octad) (c : golay)
    (hc : (support c.val ∩ O.val).card=2) (χ ψ : Module.Dual Bit BinaryFour) :
    (∑ t : BinaryFour,binaryFourWalshEntry χ t*binaryFourWalshEntry ψ t)=
      if χ=ψ then (16 : Scalar) else 0 := by
  let e := octadDuadPolarEquiv O c hc
  have h := binaryQuadratic_polar_sign_pair_sum (octadQuadraticRestriction O c)
    (octadQuadraticWord_rank_duad O c hc) (e.symm χ) (e.symm ψ)
  dsimp only [e] at h
  simpa only [octadDuadPolarEquiv_symm_apply,
    (octadDuadPolarEquiv O c hc).symm.injective.eq_iff,binaryFourWalshEntry] using h

end Atlas.Fischer
