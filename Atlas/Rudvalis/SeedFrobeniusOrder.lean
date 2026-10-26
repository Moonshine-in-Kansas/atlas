import Atlas.Rudvalis.SeedAFibreOrbit
import Atlas.Rudvalis.SeedFrobenius

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem seedTMonomial_cube : seedTMonomial^3=1 := by
  apply SemidirectProduct.ext
  · rfl
  · change (seedTCoord⁻¹)^3=1
    rw [inv_pow,seedTCoord_cube,inv_one]

theorem codeT_cube : codeT^3=1 := by
  apply Subtype.ext
  change (seedConjugateHom seedTMonomial)^3=1
  rw [←map_pow,seedTMonomial_cube,map_one]

theorem codeT_ne_one : codeT≠1 := by
  intro h
  have he := congrArg (fun g : codeGroup => g.val.right (originalCoordinateEquiv (1,0))) h
  change (seedConjugateMonomial seedTMonomial).right (originalCoordinateEquiv (1,0))=
    originalCoordinateEquiv (1,0) at he
  rw [seedConjugateMonomial_right,original_congr_apply] at he
  have hc := originalCoordinateEquiv.injective he
  have hn : seedTMonomial.right (1,0)≠(1,0) := by decide +kernel
  exact hn hc

theorem codeT_order : orderOf codeT=3 := orderOf_eq_prime codeT_cube codeT_ne_one

end Atlas.Rudvalis
