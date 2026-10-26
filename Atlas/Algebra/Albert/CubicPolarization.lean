import Atlas.Algebra.Albert.TraceZeroForms

/-! Full cubic polarization with the normalization used by the Ree coordinate
sources. The characteristic-two alternating polarization does not by itself
recover the cubic polynomial. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

private theorem norm_sum (x y : Carrier F) : norm (x+y) = norm x +
    tracePairing (adjoint x) y + tracePairing x (adjoint y) + norm y := by
  simpa using norm_add_smul (1 : F) x y

private theorem pairing_add_right (x y z : Carrier F) :
    tracePairing x (y+z) = tracePairing x y + tracePairing x z := by
  rw [tracePairing_comm, tracePairing_add_left, tracePairing_comm y,
    tracePairing_comm z]

private theorem pairing_sub_left (x y z : Carrier F) :
    tracePairing (x-y) z = tracePairing x z - tracePairing y z := by
  rw [sub_eq_add_neg, tracePairing_add_left, ← neg_one_smul F y,
    tracePairing_smul_left]
  ring

theorem norm_fullPolarization (x y z : Carrier F) :
    norm (x+y+z) - norm (x+y) - norm (x+z) - norm (y+z) +
      norm x + norm y + norm z = tracePairing (cross x y) z := by
  rw [norm_sum (x+y) z, norm_sum x z, norm_sum y z]
  rw [cross, pairing_sub_left, pairing_sub_left, tracePairing_add_left]
  ring

variable [CharP F 2]

theorem traceZeroCubic_fullPolarization (u v w : TraceZero F) :
    traceZeroCubic (u+v+w) + traceZeroCubic (u+v) + traceZeroCubic (u+w) +
      traceZeroCubic (v+w) + traceZeroCubic u + traceZeroCubic v + traceZeroCubic w =
        traceZeroPolar (traceZeroCross u v) w := by
  rw [traceZeroPolar_cross]
  simpa only [traceZeroCubic, Submodule.coe_add, sub_eq_add_neg, CharTwo.neg_eq]
    using norm_fullPolarization (u : Carrier F) v w

end Atlas.Albert
