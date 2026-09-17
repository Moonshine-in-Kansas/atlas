import Atlas.Fischer.ParkerSectionCosets

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerTripleIntersection_add_right (d a b c : BinaryWord) :
    parkerTripleIntersection d a (b+c)=
      parkerTripleIntersection d a b+parkerTripleIntersection d a c := by
  simp only [parkerTripleIntersection,Pi.add_apply,mul_add,Finset.sum_add_distrib]

namespace ParkerSection
variable {K : ParkerElementarySubcode}

/-- The row-to-column product sign on any actual elementary Parker coset. -/
theorem cosetLift_matrix_sign (q : ParkerSection K) (d : ParkerLoop) (a b : K.code) :
    parkerLoopMultiply (q.cosetLift d a) (q.lift (a+b)) =
      parkerSign (parkerTripleIntersection d.1 a.val b.val) (q.cosetLift d b) := by
  rw [cosetLift_multiply]
  have haa : a+(a+b)=b := by
    apply Subtype.ext
    change a.val+(a.val+b.val)=b.val
    rw [← add_assoc,parkerGolay_add_self,zero_add]
  rw [haa]
  have ht : parkerTripleIntersection d.1 a.val (a+b).val=
      parkerTripleIntersection d.1 a.val b.val := by
    change parkerTripleIntersection d.1 a.val (a.val.val+b.val.val)=_
    rw [parkerTripleIntersection_add_right,parkerTripleIntersection_repeat,zero_add]
  rw [ht]

end ParkerSection
end Atlas.Fischer
