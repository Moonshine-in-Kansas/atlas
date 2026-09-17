import Atlas.Codes.TernaryGolay
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace Atlas.Codes

def ternaryOne : ternaryGolay := ⟨fun _ => 1, ternaryGolay_one⟩

def ternaryConstants : Submodule (ZMod 3) ternaryGolay :=
  Submodule.span (ZMod 3) {ternaryOne}

abbrev TernaryPhaseModule := ternaryGolay ⧸ ternaryConstants

theorem ternaryOne_ne_zero : ternaryOne ≠ 0 := by
  intro h
  have he := congrFun (congrArg Subtype.val h) 0
  change (1 : ZMod 3) = 0 at he
  exact one_ne_zero he

theorem ternaryConstants_finrank : Module.finrank (ZMod 3) ternaryConstants = 1 :=
  finrank_span_singleton ternaryOne_ne_zero

theorem ternaryPhaseModule_finrank : Module.finrank (ZMod 3) TernaryPhaseModule = 5 := by
  have h := ternaryConstants.finrank_quotient_add_finrank
  rw [ternaryConstants_finrank, ternaryGolay_finrank] at h
  exact Nat.add_right_cancel (h.trans (by decide : 6 = 5+1))

end Atlas.Codes
