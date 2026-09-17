import Atlas.Conway.IcosianReflectionFrameGeneration
import Atlas.Conway.IcosianProjectiveModel
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
namespace Atlas.Conway

/-- The full order follows from the independent525-frame count and the full
2304-element stabilizer, after structural reflection transitivity. -/
theorem icosianHermitian_order : Nat.card icosianHermitianGroup=1209600 := by
  have ho : Nat.card (MulAction.orbit icosianHermitianGroup
      icosianLocalCoordinateRootFrame)=525 := by
    rw [MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ IcosianRootFrame),
      icosianRootFrames_card]
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup icosianHermitianGroup icosianLocalCoordinateRootFrame)
  rw [Nat.card_prod,ho,icosianLocalCoordinateRootFrame_stabilizer_card] at h
  exact h.symm

theorem icosianCentralizer_order : Nat.card icosianCentralizer=1209600 := by
  rw [← Nat.card_congr icosianCentralizerEquiv.toEquiv,icosianHermitian_order]

/-- The actual quotient by the two central signs has the Hall--Janko order. -/
theorem icosianProjective_order : Nat.card IcosianProjectiveModel=604800 := by
  have h := icosianProjective_card_mul_two
  rw [icosianHermitian_order] at h
  omega

theorem icosianProjective_order_factorization :
    Nat.card IcosianProjectiveModel=2^7*3^3*5^2*7 := by
  rw [icosianProjective_order]
  norm_num

theorem icosianHermitian_frame_order_identity :
    Nat.card icosianHermitianGroup=Nat.card IcosianRootFrame*
      Nat.card icosianCoordinateFrameStabilizer := by
  rw [icosianHermitian_order,icosianRootFrames_card,icosianCoordinateFrameStabilizer_card]

end Atlas.Conway
