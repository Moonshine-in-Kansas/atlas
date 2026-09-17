import Atlas.Algebra.GoldenFourAlternating
import Atlas.LinearGroups.PSLFieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

/-! # PSL2 over any four-element field and the actual alternating group

The map reuses the five-point projective-line action already proved in the
icosian development. A specified field isomorphism transports the PSL carrier.
-/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]

def cardFourFieldEquiv (hF : Nat.card F = 4) : F ≃+* Atlas.Algebra.GoldenFour := by
  letI := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Atlas.Algebra.goldenFour_card] using hF)

/-- The retained natural five-point action after a field-coordinate marking. -/
def psl2Card4EquivAlt5 (hF : Nat.card F = 4) : PSL(2,F) ≃* alternatingGroup (Fin 5) :=
  (Atlas.fieldEquivPSL 2 (cardFourFieldEquiv hF)).trans
    (MulEquiv.ofBijective Atlas.Algebra.goldenFourPSLToAlternating
      Atlas.Algebra.goldenFourPSLToAlternating_bijective)

theorem psl2Card4EquivAlt5_action (hF : Nat.card F = 4) (g : PSL(2,F)) :
    (psl2Card4EquivAlt5 hF g).val = Atlas.Algebra.goldenFourPSLToFivePerm
      (Atlas.fieldEquivPSL 2 (cardFourFieldEquiv hF) g) := rfl

def psl2FourEquivAlt5 : PSL(2,GaloisField 2 2) ≃* alternatingGroup (Fin 5) :=
  psl2Card4EquivAlt5 (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
end Atlas.Comparisons.Exceptional
