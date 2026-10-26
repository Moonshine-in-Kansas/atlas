import Atlas.LinearGroups.F4.Basic

namespace Atlas.F4
variable {F : Type*} [Field F]

instance faithfulLinearAction : FaithfulSMul (Model F) (Atlas.Albert.Carrier F) where
  eq_of_smul_eq_smul h := Subtype.ext (LinearEquiv.ext h)

theorem faithful_linear : FaithfulSMul (Model F) (Atlas.Albert.Carrier F) := inferInstance

end Atlas.F4
