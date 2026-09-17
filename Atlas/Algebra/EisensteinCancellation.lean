import Atlas.Algebra.EisensteinRational

namespace Atlas.Algebra

theorem eisenstein_mul_left_cancel {a b c : Eisenstein} (ha : a≠0) (h : a*b=a*c) : b=c := by
  apply eisensteinToRational_injective
  have haK : eisensteinToRational a≠0 := by
    intro hz
    apply ha
    apply eisensteinToRational_injective
    simpa using hz
  apply mul_left_cancel₀ haK
  simpa only [← map_mul] using congrArg eisensteinToRational h

end Atlas.Algebra
