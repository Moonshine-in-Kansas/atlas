import Atlas.LinearGroups.Orthogonal.SimplicityAllCharD
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Small split-D simplicity regressions independent of order formulas -/
namespace Atlas.Orthogonal.Checks

theorem d4_three_simple :
    IsSimpleGroup (ProjectiveElementary (formD 4 (ZMod 3))) :=
  projectiveD_simple_all_char 1

theorem d4_four_simple :
    IsSimpleGroup (ProjectiveElementary (formD 4 (GaloisField 2 2))) :=
  projectiveD_simple_all_char 1
end Atlas.Orthogonal.Checks
