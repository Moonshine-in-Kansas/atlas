import Atlas.LinearGroups.ReeF4.ShortRootOrder
import Mathlib.GroupTheory.OrderOfElement

/-! The source short-root element has genuine order four, not merely exponent
at most four. The nonidentity square is detected in one marked coordinate. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxHeartbeats 1000000 in
theorem shortRootEquiv_fourth : (shortRootEquiv (F := F)) ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro w
  change shortRootLinear (shortRootLinear (shortRootLinear (shortRootLinear w))) = w
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    (LinearMap.congr_fun (shortRootLinear_fourth (F := F)) w)

theorem shortRootEquiv_square_ne_one [Nontrivial F] :
    (shortRootEquiv (F := F)) ^ 2 ≠ 1 := by
  intro h
  have hw := congrArg
    (fun e : TraceZero F ≃ₗ[F] TraceZero F => (e (rootVector (2,1))).val.2 1 0) h
  change (shortRootLinear (shortRootLinear (rootVector (F := F) (2,1)))).val.2 1 0 =
    (rootVector (F := F) (2,1)).val.2 1 0 at hw
  rw [← shortRootCoordinateLinear_eq] at hw
  norm_num [shortRootCoordinateLinear, shortRootFormula, rootVector, Pi.single_apply,
    show (1 : Fin 3) ≠ 2 by decide] at hw

theorem shortRootEquiv_order [Nontrivial F] : orderOf (shortRootEquiv (F := F)) = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  simpa using (orderOf_eq_prime_pow (p := 2) (n := 1)
    (shortRootEquiv_square_ne_one (F := F)) (shortRootEquiv_fourth (F := F)))

end Atlas.ReeF4
