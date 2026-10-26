import Atlas.Rudvalis.GaussianFrame

namespace Atlas.Rudvalis

noncomputable def gaussianCoordinateFrameStabilizer : Subgroup gaussianLatticeGroup where
  carrier := {f | ∀c,c∈coordinateFrame ↔ f • c∈coordinateFrame}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg c
    simpa only [mul_smul] using (hg c).trans (hf (g • c))
  inv_mem' := by
    intro f hf c
    simpa using (hf (f⁻¹ • c)).symm

theorem gaussianCoordinateFrameStabilizer_eq_range :
    gaussianCoordinateFrameStabilizer=codeGaussianHom.range := by
  ext f
  exact gaussian_frame_stabilizer f

noncomputable def gaussianFrameStabilizerEquiv : codeGroup ≃* gaussianCoordinateFrameStabilizer :=
  (MonoidHom.ofInjective codeGaussianHom_injective).trans
    (MulEquiv.subgroupCongr gaussianCoordinateFrameStabilizer_eq_range.symm)

theorem gaussianCoordinateFrameStabilizer_order :
    Nat.card gaussianCoordinateFrameStabilizer=1376256 := by
  rw [Nat.card_congr gaussianFrameStabilizerEquiv.symm.toEquiv]
  exact codeGroup_order

end Atlas.Rudvalis
