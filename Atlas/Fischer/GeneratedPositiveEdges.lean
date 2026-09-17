import Atlas.Fischer.GeneratedAlgebraParity
import Atlas.Fischer.ReflectingUnitGraph
import Atlas.Algebra.ConnectedInvolutionPairs

noncomputable section
namespace Atlas.Fischer

def rootGeneratedAlgebraEdgePairs (Γ : SimpleGraph ReflectingRootParameter) : Set rootGeneratedAlgebraGroup :=
  {g | ∃ i j, Γ.Adj i j ∧ g=displayedAlgebraRootElement i * displayedAlgebraRootElement j}

/-- Connected root-pair geometry generates the positive algebra subgroup. -/
theorem rootGeneratedAlgebraParity_kernel_edges (Γ : SimpleGraph ReflectingRootParameter)
    (hΓ : Γ.Connected) :
    rootGeneratedAlgebraParity.ker=Subgroup.closure (rootGeneratedAlgebraEdgePairs Γ) := by
  rw [rootGeneratedAlgebraParity_kernel_pairs]
  exact Atlas.Algebra.connected_involution_pairs_generate displayedAlgebraRootElement
    displayedAlgebraRootElement_mul_self Γ hΓ

theorem displayedAlgebraRootElement_unit_square (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=1) :
    (displayedAlgebraRootElement i * displayedAlgebraRootElement j)^2=1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change rootMap (reflectingRootParameterVector i) (rootMap (reflectingRootParameterVector j)
    (rootMap (reflectingRootParameterVector i) (rootMap (reflectingRootParameterVector j) x)))=x
  rw [reflectingRoot_unit_product_square _ _ (reflectingRootParameter_isReflectingRoot i)
    (reflectingRootParameter_isReflectingRoot j) (by rw [h]; norm_num),h,one_smul]

theorem displayedAlgebraRootElement_zero_cube (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0) :
    (displayedAlgebraRootElement i * displayedAlgebraRootElement j)^3=1 := by
  apply Subtype.ext
  exact reflectingRootAutomorphism_product_cube _ _ (reflectingRootParameter_isReflectingRoot i)
    (reflectingRootParameter_isReflectingRoot j) h

end Atlas.Fischer
