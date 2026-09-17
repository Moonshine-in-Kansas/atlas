import Atlas.Conway.EisensteinFullGeneration
import Atlas.Conway.EisensteinTransitiveOrder

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

theorem eisensteinHermitian_order : Nat.card eisensteinHermitianGroup=2690072985600 :=
  eisensteinHermitian_order_of_transitive eisensteinHermitian_frame_transitive

theorem eisensteinCentralizer_order : Nat.card eisensteinCentralizer=2690072985600 :=
  eisensteinCentralizer_order_of_transitive eisensteinHermitian_frame_transitive

theorem eisensteinHermitian_frame_order_identity :
    Nat.card eisensteinHermitianGroup =
      Nat.card EisensteinFrame * Nat.card eisensteinCoordinateFrameStabilizer := by
  rw [eisensteinHermitian_order,eisensteinFrame_card,eisensteinFullFrameStabilizer_order]

theorem eisensteinCentralizer_scalar_order_identity :
    Nat.card eisensteinCentralizer = Nat.card EisensteinProjectiveModel * 6 := by
  have h := eisensteinCentralizerScalars.card_eq_card_quotient_mul_card_subgroup
  rw [eisensteinCentralizerScalars_order] at h
  exact h

theorem eisensteinCentralizer_six_dvd : 6 ∣ Nat.card eisensteinCentralizer :=
  ⟨Nat.card EisensteinProjectiveModel,by rw [eisensteinCentralizer_scalar_order_identity,mul_comm]⟩

theorem eisensteinProjective_order : Nat.card EisensteinProjectiveModel=448345497600 :=
  eisensteinProjective_order_of_transitive eisensteinHermitian_frame_transitive

theorem eisensteinProjective_order_factorization :
    Nat.card EisensteinProjectiveModel=2^13*3^7*5^2*7*11*13 := by
  rw [eisensteinProjective_order]
  norm_num

theorem eisensteinHermitianQuotient_order : Nat.card EisensteinHermitianQuotient=448345497600 :=
  eisensteinHermitianQuotient_order_of_transitive eisensteinHermitian_frame_transitive

end Atlas.Conway
