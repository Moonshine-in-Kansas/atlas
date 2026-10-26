import Atlas.Rudvalis.HeavyCrossScalarRigidity
import Atlas.Rudvalis.LocalBridgeCommonEnergy

namespace Atlas.Rudvalis

theorem gaussianUnits_cross_trivial (u : GaussianUnits) (c : MinimalCross) : u.val • c=c := by
  induction c using Quotient.inductionOn with
  | h v =>
    change u.val • minimalCross v=minimalCross v
    rw [←minimalCross_smul]
    exact (minimalCross_eq_iff _ _).mpr ⟨u,rfl⟩

theorem code_coordinate_frame_heavy_scalar (g : codeGroup)
    (hg : ∀i : Coordinate,g • coordinateCross i=coordinateCross i)
    (w : HeavyMinimumWords)
    (hw : g • minimalCross (minimumWordShellLift (heavyMinimumWord w))=
      minimalCross (minimumWordShellLift (heavyMinimumWord w))) :
    ∃u : GaussianUnits,u.val=g := by
  have hi := Subgroup.mem_zpowers codeI
  rcases code_fix_coordinateCross_permutation g hg with hp|hp
  · rcases code_sign_heavy_cross_scalar g hp w hw with he|he
    · exact ⟨1,he.symm⟩
    · exact ⟨⟨codeI^2,Subgroup.pow_mem _ hi 2⟩,he.symm⟩
  · let k := codeI⁻¹*g
    have hk : k.val.right=1 := by
      change codeI.val.right⁻¹*g.val.right=1
      rw [hp,inv_mul_cancel]
    have hf : k • minimalCross (minimumWordShellLift (heavyMinimumWord w))=
        minimalCross (minimumWordShellLift (heavyMinimumWord w)) := by
      dsimp [k]
      rw [mul_smul,hw]
      exact gaussianUnits_cross_trivial ⟨codeI⁻¹,Subgroup.inv_mem _ hi⟩ _
    have hm : k∈GaussianUnits := by
      rcases code_sign_heavy_cross_scalar k hk w hf with he|he
      · rw [he];exact Subgroup.one_mem _
      · rw [he];exact Subgroup.pow_mem _ hi 2
    refine ⟨⟨codeI*k,Subgroup.mul_mem _ hi hm⟩,?_⟩
    dsimp [k]
    exact mul_inv_cancel_left _ _

theorem gaussian_coordinate_frame_heavy_scalar (g : gaussianLatticeGroup)
    (hg : ∀i : Coordinate,g • coordinateCross i=coordinateCross i)
    (w : HeavyMinimumWords)
    (hw : g • minimalCross (minimumWordShellLift (heavyMinimumWord w))=
      minimalCross (minimumWordShellLift (heavyMinimumWord w))) :
    ∃u : GaussianUnits,codeGaussianHom u.val=g := by
  have hfix : ∀c∈coordinateFrame,g • c=c := by
    intro c hc
    obtain ⟨i,rfl⟩ := coordinateFrame_rep c hc
    exact hg i
  have hf : ∀c,c∈coordinateFrame ↔ g • c∈coordinateFrame := by
    intro c
    constructor
    · intro hc;rw [hfix c hc];exact hc
    · intro hc
      have he := hfix (g • c) hc
      have hh : g • c=c := (MulAction.injective g) he
      rwa [hh] at hc
  obtain ⟨k,rfl⟩ := (gaussian_frame_stabilizer g).mp hf
  simp only [codeGaussianHom_cross] at hg hw
  obtain ⟨u,hu⟩ := code_coordinate_frame_heavy_scalar k hg w hw
  exact ⟨u,congrArg codeGaussianHom hu⟩


/-- Fixing a cross and its entire perpendicular shell leaves only the four Gaussian scalars. -/
theorem gaussian_reference_perpendicular_kernel (g : gaussianLatticeGroup)
    (hx : g • localReferenceCross=localReferenceCross)
    (hy : ∀c : MinimalCross,CrossOrthogonal localReferenceCross c → g • c=c) :
    ∃u : GaussianUnits,codeGaussianHom u.val=g := by
  have hframe : ∀i : Coordinate,g • coordinateCross i=coordinateCross i := by
    intro i
    by_cases he : localReferenceCross=coordinateCross i
    · simpa only [←he] using hx
    · apply hy
      apply (coordinateFrame_orthogonal_iff _ _ _ (coordinateCross_mem _)).mpr he
      rw [localReferenceCross_eq]
      exact coordinateCross_mem _
  obtain ⟨c,hc⟩ := localHeavyBridgeCross_heavy
  obtain ⟨w,hw⟩ := heavyCross_rep c
  apply gaussian_coordinate_frame_heavy_scalar g hframe w
  have he := hw.symm.trans hc
  rw [he]
  exact hy _ localHeavyBridgeCross_common.1

/-- The complete cross-action kernel consists of actual Gaussian scalar lattice isometries. -/
theorem gaussian_cross_kernel_scalar (g : gaussianLatticeGroup)
    (hg : ∀c : MinimalCross,g • c=c) :
    ∃u : GaussianUnits,codeGaussianHom u.val=g :=
  gaussian_reference_perpendicular_kernel g (hg _) (fun c _ => hg c)

end Atlas.Rudvalis
