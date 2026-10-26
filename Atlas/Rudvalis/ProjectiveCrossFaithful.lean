import Atlas.Rudvalis.ProjectiveCrossAction
import Atlas.Rudvalis.StrongCrossKernel

namespace Atlas.Rudvalis

theorem gaussian_cross_kernel_eq_scalars :
    (MulAction.toPermHom gaussianLatticeGroup MinimalCross).ker=gaussianScalarSubgroup := by
  apply le_antisymm
  · intro g hg
    have hf : ∀c : MinimalCross,g • c=c := fun c => congrArg (fun e : Equiv.Perm MinimalCross => e c) hg
    obtain ⟨u,hu⟩ := gaussian_cross_kernel_scalar g hf
    exact ⟨u.val,u.prop,hu⟩
  · exact gaussianScalarSubgroup_cross_kernel

theorem rudvalis_cross_faithful : FaithfulSMul RudvalisGroup MinimalCross := by
  apply faithfulSMul_iff.mpr
  intro g
  induction g using QuotientGroup.induction_on with
  | H g =>
    intro hg
    obtain ⟨u,hu⟩ := gaussian_cross_kernel_scalar g hg
    exact (QuotientGroup.eq_one_iff g).mpr ⟨u.val,u.prop,hu⟩

/-- Strong scalar rigidity holds at every actual lattice cross. -/
theorem gaussian_perpendicular_kernel (x : MinimalCross) (g : gaussianLatticeGroup)
    (hx : g • x=x)
    (hy : ∀c : MinimalCross,CrossOrthogonal x c → g • c=c) :
    ∃u : GaussianUnits,codeGaussianHom u.val=g := by
  let := full_gaussian_cross_transitive
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq gaussianLatticeGroup localReferenceCross x
  have hf : (a⁻¹*g*a) • localReferenceCross=localReferenceCross := by
    rw [mul_smul,mul_smul,ha,hx,←ha,inv_smul_smul]
  have hh (c : MinimalCross) (hc : CrossOrthogonal localReferenceCross c) :
      (a⁻¹*g*a) • c=c := by
    rw [mul_smul,mul_smul,hy]
    · exact inv_smul_smul a c
    · rw [←ha]
      exact (crossOrthogonal_gaussian a _ _).mpr hc
  obtain ⟨u,hu⟩ := gaussian_reference_perpendicular_kernel (a⁻¹*g*a) hf hh
  have hs : codeGaussianHom u.val∈gaussianScalarSubgroup := ⟨u.val,u.prop,rfl⟩
  have hc := Subgroup.mem_center_iff.mp (gaussianScalarSubgroup_le_center hs) a
  refine ⟨u,?_⟩
  have he := congrArg (fun k : gaussianLatticeGroup => a*k*a⁻¹) hu
  simpa only [←mul_assoc,mul_inv_cancel,one_mul,mul_assoc,inv_mul_cancel,mul_one,hc,mul_inv_cancel_left] using he

theorem rudvalis_perpendicular_kernel (x : MinimalCross) (g : RudvalisGroup)
    (hx : g • x=x)
    (hy : ∀c : MinimalCross,CrossOrthogonal x c → g • c=c) : g=1 := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨u,hu⟩ := gaussian_perpendicular_kernel x g hx hy
    exact (QuotientGroup.eq_one_iff g).mpr ⟨u.val,u.prop,hu⟩

end Atlas.Rudvalis
