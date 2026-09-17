import Atlas.Fischer.ParkerLoopIdentities

namespace Atlas.Fischer
open Atlas.Codes

/-- An actual permutation of the loop, with the required sign correction. -/
def parkerLoopLift (g : golay ≃ₗ[Bit] golay) (η : golay → Bit) : Equiv.Perm ParkerLoop where
  toFun x := (g x.1, x.2 + η x.1)
  invFun x := (g.symm x.1, x.2 + η (g.symm x.1))
  left_inv x := by
    apply Prod.ext
    · exact g.symm_apply_apply _
    · simp only [g.symm_apply_apply]
      have h : ∀ b : Bit, b + b = 0 := by decide
      simp only [add_assoc, h, add_zero]
  right_inv x := by
    apply Prod.ext
    · exact g.apply_symm_apply _
    · have h : ∀ b : Bit, b + b = 0 := by decide
      simp only [add_assoc, h, add_zero]

theorem parkerLoopLift_preserves_multiply (g : golay ≃ₗ[Bit] golay) (η : golay → Bit)
    (hη : ∀ a b, η (a + b) + η a + η b =
      parkerGolayFactorSet (g a) (g b) + parkerGolayFactorSet a b) (x y : ParkerLoop) :
    parkerLoopLift g η (parkerLoopMultiply x y) =
      parkerLoopMultiply (parkerLoopLift g η x) (parkerLoopLift g η y) := by
  apply Prod.ext
  · exact g.map_add _ _
  · change x.2 + y.2 + parkerGolayFactorSet x.1 y.1 + η (x.1 + y.1) =
      x.2 + η x.1 + (y.2 + η y.1) + parkerGolayFactorSet (g x.1) (g y.1)
    have h := congrArg (fun z => z + x.2 + y.2 + η x.1 + η y.1 +
      parkerGolayFactorSet x.1 y.1) (hη x.1 y.1)
    convert h using 1 <;> ring_nf <;>
      simp only [show (2 : Bit) = 0 from rfl, mul_zero, zero_add, add_zero]

theorem parkerLoopLift_sign (g : golay ≃ₗ[Bit] golay) (η : golay → Bit)
    (s : Bit) (x : ParkerLoop) :
    parkerLoopLift g η (parkerSign s x) = parkerSign s (parkerLoopLift g η x) := by
  apply Prod.ext
  · rfl
  · change x.2 + s + η x.1 = x.2 + η x.1 + s
    ring

theorem parkerLoopLift_fixes_sign (g : golay ≃ₗ[Bit] golay) (η : golay → Bit)
    (hη : η 0 = 0) (s : Bit) : parkerLoopLift g η (0, s) = (0, s) := by
  simp [parkerLoopLift, hη]

end Atlas.Fischer
