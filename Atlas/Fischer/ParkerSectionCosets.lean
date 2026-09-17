import Atlas.Fischer.ParkerSections
import Atlas.Fischer.ParkerLoopIdentities

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
namespace ParkerSection
variable {K : ParkerElementarySubcode}

/-- Actual left-coset labels, before imposing an octad-weight condition. -/
def cosetLift (q : ParkerSection K) (d : ParkerLoop) (a : K.code) : ParkerLoop :=
  parkerLoopMultiply d (q.lift a)

@[simp] theorem cosetLift_code (q : ParkerSection K) (d : ParkerLoop) (a : K.code) :
    (q.cosetLift d a).1 = d.1 + a.val := rfl

/-- The complete Parker sign in a section-coset multiplication is its actual
triple-intersection associator, with no choice of sign gauge assumed. -/
theorem cosetLift_multiply (q : ParkerSection K) (d : ParkerLoop) (a b : K.code) :
    parkerLoopMultiply (q.cosetLift d a) (q.lift b) =
      parkerSign (parkerTripleIntersection d.1 a.val b.val) (q.cosetLift d (a+b)) := by
  unfold cosetLift
  rw [parkerLoopMultiply_associator,← q.lift_multiply]
  rfl

theorem cosetLift_injective (q : ParkerSection K) (d : ParkerLoop) :
    Function.Injective (q.cosetLift d) := by
  intro a b h
  have hc := congrArg Prod.fst h
  change d.1+a.val=d.1+b.val at hc
  exact Subtype.ext (add_left_cancel hc)

/-- Changing the section changes only the diagonal sign of each actual coset label. -/
theorem cosetLift_translate (q : ParkerSection K) (l : Module.Dual Bit K.code)
    (d : ParkerLoop) (a : K.code) :
    (q.translate l).cosetLift d a = parkerSign (l a) (q.cosetLift d a) := by
  unfold cosetLift
  rw [translate_lift,parkerLoopMultiply_sign_right]

end ParkerSection
end Atlas.Fischer
