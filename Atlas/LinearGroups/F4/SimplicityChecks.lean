import Atlas.LinearGroups.F4.Simplicity
import Mathlib.FieldTheory.Finite.GaloisField

/-! Separate all-characteristic simplicity regressions. Numerical group-order
checks are intentionally not imported into this scope. -/
namespace Atlas.F4.SimplicityChecks
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem binary_simple : IsSimpleGroup (Model (ZMod 2)) := isSimple
theorem ternary_simple : IsSimpleGroup (Model (ZMod 3)) := isSimple
theorem four_simple : IsSimpleGroup (Model (GaloisField 2 2)) := isSimple
theorem five_simple : IsSimpleGroup (Model (ZMod 5)) := isSimple
theorem eight_simple : IsSimpleGroup (Model (GaloisField 2 3)) := isSimple

end Atlas.F4.SimplicityChecks
