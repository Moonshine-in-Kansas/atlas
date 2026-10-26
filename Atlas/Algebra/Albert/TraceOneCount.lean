import Atlas.Algebra.Albert.WhiteConeCount
import Atlas.Algebra.Albert.TraceNormalization

namespace Atlas.Albert
variable {F : Type*} [Field F] [Finite F]

theorem card_traceOneRankOne : Nat.card (TraceOneRankOne F) =
    Nat.card F^8*(Nat.card F^8+Nat.card F^4+1) := by
  have hs := Atlas.card_predicate_split (fun x : Carrier F => adjoint x=0)
    (fun x => trace x=0)
  rw [card_adjoint_zero,card_white_cone,
    Nat.card_congr (nonzeroTraceEquiv (F:=F)),Nat.card_prod,Nat.card_units] at hs
  have hp := traceOne_count_polynomial (Nat.card F)
    (by have := Finite.one_lt_card (α:=F); omega)
  have he : (Nat.card F-1)*Nat.card (TraceOneRankOne F) =
      (Nat.card F-1)*(Nat.card F^8*(Nat.card F^8+Nat.card F^4+1)) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by have := Finite.one_lt_card (α:=F); omega) he

end Atlas.Albert
