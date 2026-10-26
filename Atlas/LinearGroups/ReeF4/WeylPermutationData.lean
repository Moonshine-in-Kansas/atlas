import Atlas.LinearGroups.ReeF4.WeylCoordinates
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace Atlas.ReeF4
abbrev WeylCoordinate := Fin 3 × Fin 9

def weylRhoIndex (p : WeylCoordinate) : WeylCoordinate :=
  (p.1, (![![(0 : Fin 9),1,6,5,4,3,2,7,8],
    ![1,0,3,2,4,6,5,8,7], ![1,0,5,6,4,2,3,8,7]]) p.1 p.2)

def weylSigmaIndex (p : WeylCoordinate) : WeylCoordinate :=
  ((![(2 : Fin 3),1,0]) p.1,
    (![(0 : Fin 9),2,1,5,4,3,7,6,8]) p.2)

def weylRhoPermutation : Equiv.Perm WeylCoordinate :=
  ⟨weylRhoIndex, weylRhoIndex, by decide, by decide⟩

def weylSigmaPermutation : Equiv.Perm WeylCoordinate :=
  ⟨weylSigmaIndex, weylSigmaIndex, by decide, by decide⟩

def weylDihedralPermutation : DihedralGroup 8 → Equiv.Perm WeylCoordinate
  | .r i => (weylRhoPermutation * weylSigmaPermutation) ^ i.val
  | .sr i => weylRhoPermutation * (weylRhoPermutation * weylSigmaPermutation) ^ i.val

end Atlas.ReeF4
