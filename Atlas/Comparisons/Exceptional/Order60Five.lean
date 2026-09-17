import Mathlib.Algebra.Field.ZMod
import Atlas.GroupTheory.SimpleOrderSixty
import Atlas.LinearGroups.PSLSimplicityChecks
import Atlas.Comparisons.Exceptional.Order60Four

/-! # PSL2 over five-element fields and A5 by elementary Sylow recognition -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups
local instance order60FivePrime1 : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {F : Type*} [Field F] [Finite F]

/-- The degree-five coset action constructed by elementary order-sixty recognition. -/
def psl2Card5EquivAlt5 (hF : Nat.card F = 5) : PSL(2,F) ≃* alternatingGroup (Fin 5) := by
  have h := Atlas.psl_two_five_check hF
  letI := h.1
  exact Atlas.GroupTheory.smallSimpleOrder60EquivAlt5 (PSL(2,F)) h.2.2 h.2.1

def psl2FiveEquivAlt5 : PSL(2,ZMod 5) ≃* alternatingGroup (Fin 5) :=
  psl2Card5EquivAlt5 (F := ZMod 5) (by rw [Nat.card_eq_fintype_card, ZMod.card])

/-- Regression of the abstract recognition theorem; the public q=4 map remains the natural projective action. -/
def psl2Card4RecognitionEquivAlt5 (hF : Nat.card F = 4) : PSL(2,F) ≃* alternatingGroup (Fin 5) := by
  have h := Atlas.psl_two_four_check hF
  letI := h.1
  exact Atlas.GroupTheory.smallSimpleOrder60EquivAlt5 (PSL(2,F)) h.2.2 h.2.1

def psl2Card4EquivPsl2Five (hF : Nat.card F = 4) : PSL(2,F) ≃* PSL(2,ZMod 5) :=
  (psl2Card4EquivAlt5 hF).trans psl2FiveEquivAlt5.symm

def psl2FourEquivPsl2Five : PSL(2,GaloisField 2 2) ≃* PSL(2,ZMod 5) :=
  psl2FourEquivAlt5.trans psl2FiveEquivAlt5.symm

end Atlas.Comparisons.Exceptional
