import Atlas.Fischer.ParkerSectionCounting

namespace Atlas.Fischer
open Atlas.Codes

/-- Cancellation in the actual Parker loop, derived from its explicit division. -/
theorem parkerLoopMultiply_left_injective (x : ParkerLoop) :
    Function.Injective (parkerLoopMultiply x) := by
  intro y z h
  have he := congrArg (parkerLeftDivide parkerGolayFactorSet x) h
  simpa only [parkerLoopMultiply,parkerLeftDivide_multiply] using he

namespace ParkerSection
variable {K : ParkerElementarySubcode}

/-- Calibration at a prescribed element of the retained loop. -/
def LiftCalibrated (a : K.code) (d : ParkerLoop) :=
  {q : ParkerSection K // q.lift a = d}

def liftCalibrationEquiv (a : K.code) (d : ParkerLoop) (hd : d.1=a.val) :
    LiftCalibrated a d ≃ Calibrated a d.2 where
  toFun q := ⟨q.val,congrArg Prod.snd q.property⟩
  invFun q := ⟨q.val,Prod.ext hd.symm q.property⟩
  left_inv q := rfl
  right_inv q := rfl

theorem lift_calibrated_card (a : K.code) (ha : a ≠ 0) (d : ParkerLoop)
    (hd : d.1=a.val) : Nat.card (LiftCalibrated a d) = Nat.card K.code / 2 := by
  rw [Nat.card_congr (liftCalibrationEquiv a d hd),calibrated_card a ha d.2]

theorem exists_omega_calibrated (a : K.code) (ha : a ≠ 0) (o : ParkerLoop)
    (hc : a.val = golayOne+o.1) :
    ∃ q : ParkerSection K, q.lift a = parkerLoopMultiply parkerOmega o := by
  apply exists_lift a ha (parkerLoopMultiply parkerOmega o)
  exact hc.symm

/-- The unique character relating two actual sections. -/
theorem difference_lift (q r : ParkerSection K) (a : K.code) :
    r.lift a = parkerSign (q.difference r a) (q.lift a) := by
  rw [← translate_lift,q.translate_difference]

/-- Changing both calibrated choices has one and the same character correction:
its value on the complement is exactly the change in the octad lift. -/
theorem calibrated_change (q r : ParkerSection K) (a : K.code) (o o' : ParkerLoop)
    (hq : q.lift a = parkerLoopMultiply parkerOmega o)
    (hr : r.lift a = parkerLoopMultiply parkerOmega o') :
    o' = parkerSign (q.difference r a) o := by
  apply parkerLoopMultiply_left_injective parkerOmega
  rw [parkerLoopMultiply_sign_right,← hq,← hr]
  exact q.difference_lift r a

end ParkerSection
end Atlas.Fischer
