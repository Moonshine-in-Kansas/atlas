import Atlas.LinearGroups.ReeF4.PositiveRootTail
import Atlas.LinearGroups.ReeF4.AlternatingFactorSimp
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.WeylRhoDerived

/-!
Source-only draft, 27 October 2026; no compiler or checker has been run.
The import `FamilyWork.PositiveRootTail` means the parent's staged copy of the
preserved earlier tail draft. This file does not duplicate that construction.

The actual rho operator permutes the seven tail factors, with unchanged root
parameters. The coordinate checks have fixed size (three short and four long
operators on the 27 ambient coordinates); no field or group is enumerated.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Rho on the existing Albert carrier, in the inherited octonion ordering. -/
def tailRhoCarrier (w : Carrier F) : Carrier F :=
  (w.1,
    ![![w.2 0 0, w.2 0 1, w.2 0 5, w.2 0 4,
        w.2 0 3, w.2 0 2, w.2 0 6, w.2 0 7],
      ![w.2 1 1, w.2 1 0, w.2 1 3, w.2 1 2,
        w.2 1 5, w.2 1 4, w.2 1 7, w.2 1 6],
      ![w.2 2 1, w.2 2 0, w.2 2 4, w.2 2 5,
        w.2 2 2, w.2 2 3, w.2 2 7, w.2 2 6]])

theorem tailRhoCarrier_model (m : ℕ) (w : TraceZero F) :
    ((weylRhoModel m).val w).val = tailRhoCarrier w.val := by
  apply wilsonCoordinatesEquiv.injective
  change wilsonCoordinatesEquiv (weylRho w : Carrier F) = _
  rw [weylRho_coordinates]
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

end Atlas.ReeF4
