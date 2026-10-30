import Atlas.LinearGroups.ReeF4.TailRhoData
import Atlas.LinearGroups.ReeF4.TailRhoShort0
import Atlas.LinearGroups.ReeF4.TailRhoShort1
import Atlas.LinearGroups.ReeF4.TailRhoShort2
import Atlas.LinearGroups.ReeF4.TailRhoLong0
import Atlas.LinearGroups.ReeF4.TailRhoLong1
import Atlas.LinearGroups.ReeF4.TailRhoLong2
import Atlas.LinearGroups.ReeF4.TailRhoLong3

/-! Separate group-level layer of the rho normalizer proof.
The prior statements and proof bodies are preserved; verification is recorded separately. -/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem tailRhoCarrier_short (m : ℕ) (k : Fin 3) (a b : F) (w : Carrier F) :
    tailRhoCarrier (alternatingShortFormula m k.succ a b w) =
      alternatingShortFormula m (Fin.rev k).succ a b (tailRhoCarrier w) := by
  fin_cases k
  · exact tailRhoCarrier_short_0 m a b w
  · exact tailRhoCarrier_short_1 m a b w
  · exact tailRhoCarrier_short_2 m a b w

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem tailRhoCarrier_long (m : ℕ) (k : Fin 4) (u : F) (w : Carrier F) :
    tailRhoCarrier (alternatingLongFormula m k u w) =
      alternatingLongFormula m (Fin.rev k) u (tailRhoCarrier w) := by
  fin_cases k
  · exact tailRhoCarrier_long_0 m u w
  · exact tailRhoCarrier_long_1 m u w
  · exact tailRhoCarrier_long_2 m u w
  · exact tailRhoCarrier_long_3 m u w

end Atlas.ReeF4
