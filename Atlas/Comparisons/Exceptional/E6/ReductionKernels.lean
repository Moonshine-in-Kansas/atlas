import Atlas.Comparisons.Exceptional.E6.TernaryChart
import Atlas.Comparisons.Exceptional.E6.Polar

/-! Exact radicals and the kernel of the quotient chart. These are vector-space
calculations, not group-order or recognition certificates. -/
namespace Atlas.Comparisons.E6Lattice
open Matrix

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Exhaust the 64 vectors, with reduction checked by the ordinary Lean kernel.
theorem binary_radical (x : Fin 6 → ZMod 2) :
    gram.map (Int.castRingHom (ZMod 2)) *ᵥ x = 0 ↔ x = 0 := by
  revert x
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Exhaust the 729 vectors in the concrete ternary quadratic space.
theorem quotient_kernel (x : Fin 6 → ZMod 3) :
    quotientCoordinates x = 0 ↔ ternaryGram *ᵥ x = 0 := by
  revert x
  decide

theorem radicalVector_injective : Function.Injective radicalVector := by
  intro a b h
  have := congrArg (fun x : Fin 6 → ZMod 3 => x 0) h
  simpa [radicalVector] using this

def quotientProjectionLinear : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 5 → ZMod 3) where
  toFun := quotientCoordinates
  map_add' x y := by funext i; fin_cases i <;> simp [quotientCoordinates] <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp [quotientCoordinates] <;> ring

theorem quotientProjection_surjective : Function.Surjective quotientProjectionLinear :=
  fun y => ⟨quotientSection y,quotient_section y⟩

end Atlas.Comparisons.E6Lattice
