import Atlas.GroupTheory.CenterSimpleQuotient
import Atlas.Conway.EisensteinPrimitiveSimplicity

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction

/-- Conditional structural endpoint: simplicity of the actual scalar quotient
identifies all central elements of the actual Co0 centralizer. -/
theorem eisensteinCentralizer_center_of_simple
    [IsSimpleGroup EisensteinProjectiveModel]
    (hn : ¬IsMulCommutative EisensteinProjectiveModel) :
    Subgroup.center eisensteinCentralizer=eisensteinCentralizerScalars :=
  Atlas.GroupTheory.center_eq_of_simple_quotient _ _
    eisensteinCentralizerScalars_le_center hn

/-- The same center statement in the actual Hermitian coordinate model. -/
theorem eisensteinHermitian_center_of_simple
    [IsSimpleGroup EisensteinProjectiveModel]
    (hn : ¬IsMulCommutative EisensteinProjectiveModel) :
    Subgroup.center eisensteinHermitianGroup=eisensteinScalarSubgroup := by
  letI : IsSimpleGroup EisensteinHermitianQuotient := eisensteinProjectiveComparison.isSimpleGroup
  have hq : ¬IsMulCommutative EisensteinHermitianQuotient := by
    intro h
    letI := h
    exact hn (eisensteinProjectiveComparison.surjective.isMulCommutative h)
  exact Atlas.GroupTheory.center_eq_of_simple_quotient _ _ eisensteinScalarSubgroup_le_center hq

theorem eisensteinCentralizer_center_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    Subgroup.center eisensteinCentralizer=eisensteinCentralizerScalars := by
  letI := eisensteinSimplicity_of_primitive
  exact eisensteinCentralizer_center_of_simple eisensteinNonabelian_of_primitive

theorem eisensteinHermitian_center_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    Subgroup.center eisensteinHermitianGroup=eisensteinScalarSubgroup := by
  letI := eisensteinSimplicity_of_primitive
  exact eisensteinHermitian_center_of_simple eisensteinNonabelian_of_primitive

theorem eisensteinCentralizer_center_order_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    Nat.card (Subgroup.center eisensteinCentralizer)=6 := by
  rw [eisensteinCentralizer_center_of_primitive,eisensteinCentralizerScalars_order]

theorem eisensteinHermitian_center_order_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    Nat.card (Subgroup.center eisensteinHermitianGroup)=6 := by
  rw [eisensteinHermitian_center_of_primitive,eisensteinScalarSubgroup_order]

end Atlas.Conway
