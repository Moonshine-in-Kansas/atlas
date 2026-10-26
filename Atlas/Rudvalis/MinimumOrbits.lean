import Atlas.Rudvalis.FourMinimumOrbit
import Atlas.Rudvalis.HeavyMinimumOrbit
import Atlas.Rudvalis.MinimumCount

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Every minimum word lies in one of the two literal seed orbits. -/
theorem quaternary_minimum_two_seed_orbits (w : QuaternaryWord)
    (hw : w∈quaternaryCode) (hweight : euclideanWeight w=16) :
    (∃g : codeGroup,monomialHom g.val (quaternarySeed (0,0,0,0))=w) ∨
    (∃g : codeGroup,monomialHom g.val heavySeedSignedLift.val.val=w) := by
  rcases quaternary_minimum_support_cases w hw hweight with h | h
  · exact Or.inl (four_minimum_seed_orbit w hw hweight h)
  · exact Or.inr (heavy_minimum_seed_orbit w hw hweight h)

end Atlas.Rudvalis
