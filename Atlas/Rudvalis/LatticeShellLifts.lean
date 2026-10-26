import Atlas.Rudvalis.LatticeCoordinates
import Atlas.Rudvalis.MinimumCount
import Atlas.Codes.QuaternaryIntegerLift

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

def integerLift (w : QuaternaryWord) : IntegerCoordinates := fun i => integerRepresentative (w i)

theorem integerLift_reduce (w : QuaternaryWord) : reduceModFour (integerLift w)=w := by
  funext i
  exact integerRepresentative_cast (w i)

theorem integerLift_norm (w : QuaternaryWord) : integerDot (integerLift w) (integerLift w)=
    (euclideanWeight w : ℤ) := by
  simp only [integerDot,integerLift,←pow_two,integerRepresentative_sq,euclideanWeight,Nat.cast_sum]

theorem integerLift_mem (w : QuaternaryWord) (hw : w∈quaternaryCode) : integerLift w∈doubledLattice := by
  rw [doubledLattice_mem,integerLift_reduce]
  exact hw

abbrev MinimalShell := {v : rudvalisLattice // rationalDot v.val v.val=4}

noncomputable def minimumWordShellLift (w : MinimumWords) : MinimalShell :=
  ⟨⟨halfCoordinates (integerLift w.val.val),Submodule.mem_map_of_mem (integerLift_mem _ w.val.prop)⟩,by
    rw [rationalDot_half,integerLift_norm,w.prop]
    norm_num⟩

theorem minimumWordShellLift_injective : Function.Injective minimumWordShellLift := by
  intro v w h
  have he := congrArg (fun x : MinimalShell => x.val.val) h
  have hi := halfCoordinates_injective he
  have hr := congrArg reduceModFour hi
  rw [integerLift_reduce,integerLift_reduce] at hr
  exact Subtype.ext (Subtype.ext hr)

end Atlas.Rudvalis
