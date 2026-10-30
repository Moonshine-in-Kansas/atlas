import Atlas.LinearGroups.ReeF4.LineParabolicSemidirect
import Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Order.Ring.Canonical

/-!
Source-only, uncompiled. Count the actual full line stabilizer through its
specified semidirect equivalence, using only the recognized q^11 kernel
and the ordinary finite-field GL2 count. No order is used for recognition.
-/

noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F]

/-- The ordinary GL2 count, specialized directly from the standard column count. -/
theorem card_markedLineGL2 :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) =
      Nat.card F * ((Nat.card F)^2 - 1) * (Nat.card F - 1) := by
  letI := Fintype.ofFinite F
  have h : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) =
      ((Nat.card F)^2 - 1) * ((Nat.card F)^2 - Nat.card F) := by
    simpa [Fin.prod_univ_succ, Nat.card_eq_fintype_card] using
      (Matrix.card_GL_field (𝔽 := F) 2)
  have hm : (Nat.card F)^2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [h, hm]
  ac_rfl

variable [CharP F 2]

theorem card_markedLineStabilizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (markedLineStabilizer (F := F) m) =
      (Nat.card F)^12 * ((Nat.card F)^2 - 1) * (Nat.card F - 1) := by
  rw [← Nat.card_congr (lineParabolicSemidirectEquiv hcard).toEquiv,
    SemidirectProduct.card, card_markedLineRestrictionKernel hcard, card_markedLineGL2]
  ring

/-- The equivalent division-free expression in project section 8.2. -/
theorem card_markedLineStabilizer_project_form {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (markedLineStabilizer (F := F) m) =
      (Nat.card F)^12 * (Nat.card F - 1)^2 * (Nat.card F + 1) := by
  have hs : (Nat.card F)^2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    simpa only [one_pow] using sq_tsub_sq (Nat.card F) 1
  rw [card_markedLineStabilizer hcard, hs]
  ring

theorem card_markedLineStabilizer_binary
    (hcard : Nat.card F = 2 ^ (2 * 0 + 1)) :
    Nat.card (markedLineStabilizer (F := F) 0) = 12288 := by
  rw [card_markedLineStabilizer hcard, hcard]
  norm_num

end Atlas.ReeF4
