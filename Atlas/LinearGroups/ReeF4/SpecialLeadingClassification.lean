import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row15

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Allowed root coordinates for a leading special vector. This is a derived
classification, not an assumption about the model or its fixed-star witness. -/
def allowedSpecialLeadingRoot (r : Fin 26) : Prop := r ∈ ({2,4,7,9,18,19,24,25} : Finset (Fin 26))

theorem IsSpecialVector.leading_root_allowed {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (r : Fin 26) (hr : 2 ≤ r.val)
    (hn : isotropyCoordinates u r≠0)
    (hz : ∀ j, specialAbsoluteGrade r < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    allowedSpecialLeadingRoot r := by
  fin_cases r
  · norm_num at hr
  · norm_num at hr
  · unfold allowedSpecialLeadingRoot
    decide
  · exact False.elim (hn (hu.forbidden_leading_coordinate3 hcard hz))
  · unfold allowedSpecialLeadingRoot
    decide
  · exact False.elim (hn (hu.forbidden_leading_coordinate5 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate6 hcard hz))
  · unfold allowedSpecialLeadingRoot
    decide
  · exact False.elim (hn (hu.forbidden_leading_coordinate8 hcard hz))
  · unfold allowedSpecialLeadingRoot
    decide
  · exact False.elim (hn (hu.forbidden_leading_coordinate10 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate11 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate12 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate13 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate14 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate15 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate16 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate17 hcard hz))
  · unfold allowedSpecialLeadingRoot
    decide
  · unfold allowedSpecialLeadingRoot
    decide
  · exact False.elim (hn (hu.forbidden_leading_coordinate20 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate21 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate22 hcard hz))
  · exact False.elim (hn (hu.forbidden_leading_coordinate23 hcard hz))
  · unfold allowedSpecialLeadingRoot
    decide
  · unfold allowedSpecialLeadingRoot
    decide
end Atlas.ReeF4
