import Atlas.Conway.EisensteinPrimitiveSimplicity
import Atlas.Conway.EisensteinStandardFrame

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction

theorem eisensteinFrame_nontrivial : Nontrivial EisensteinFrame :=
  Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [← Nat.card_eq_fintype_card,eisensteinFrame_card]; decide)

theorem eisensteinProjectiveStabilizer_maximal_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    IsCoatom (stabilizer EisensteinProjectiveModel eisensteinStandardFrame) := by
  letI := eisensteinFrame_nontrivial
  exact IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    EisensteinProjectiveModel eisensteinStandardFrame

theorem eisensteinFullStabilizer_maximal_of_primitive
    [IsPreprimitive eisensteinHermitianGroup EisensteinFrame] :
    IsCoatom eisensteinCoordinateFrameStabilizer := by
  letI := eisensteinFrame_nontrivial
  rw [← eisensteinStandardFrame_stabilizer]
  exact IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    eisensteinHermitianGroup eisensteinStandardFrame

theorem eisensteinProjectiveStabilizer_not_normal_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    ¬(stabilizer EisensteinProjectiveModel eisensteinStandardFrame).Normal := by
  letI := eisensteinSimplicity_of_primitive
  intro hn
  rcases hn.eq_bot_or_eq_top with h|h
  · exact eisensteinProjectiveStabilizer_ne_bot h
  · exact eisensteinProjectiveStabilizer_maximal_of_primitive.ne_top h

end Atlas.Conway
