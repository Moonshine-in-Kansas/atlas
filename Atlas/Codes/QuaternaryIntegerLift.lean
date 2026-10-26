import Atlas.Codes.QuaternaryWeight
import Mathlib.Data.Int.Cast.Lemmas

namespace Atlas.Codes.Quaternary

def integerRepresentative (a : Quat) : ℤ :=
  if a=0 then 0 else if a=1 then 1 else if a=2 then 2 else -1

theorem integerRepresentative_cast (a : Quat) :
    (integerRepresentative a : Quat)=a := by
  decide +kernel +revert

theorem integerRepresentative_sq (a : Quat) :
    integerRepresentative a ^2=(euclideanSymbolWeight a : ℤ) := by
  decide +kernel +revert

theorem integerRepresentative_zero : integerRepresentative 0=0 := by decide +kernel

theorem integerRepresentative_ne_zero (a : Quat) : integerRepresentative a≠0 ↔ a≠0 := by
  decide +kernel +revert

end Atlas.Codes.Quaternary
