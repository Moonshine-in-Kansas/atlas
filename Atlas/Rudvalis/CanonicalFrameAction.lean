import Atlas.Rudvalis.FullGaussianGroup
import Atlas.Rudvalis.GaussianFrameOrder

namespace Atlas.Rudvalis

noncomputable instance canonicalFramesMulAction : MulAction gaussianLatticeGroup canonicalBases where
  smul g F := ⟨gaussianImage g F.val,(canonicalBases_gaussianImage g F.val).mpr F.prop⟩
  one_smul F := Subtype.ext (gaussianImage_one F.val)
  mul_smul g h F := Subtype.ext (gaussianImage_mul g h F.val)

noncomputable def referenceCanonicalFrame : canonicalBases :=
  ⟨coordinateFrame,coordinateFrame_isCanonicalBase⟩

theorem canonicalFrames_gaussian_pretransitive : MulAction.IsPretransitive gaussianLatticeGroup canonicalBases := by
  constructor
  intro F F'
  obtain ⟨g,hg⟩ := canonicalFrames_generated_transitive F.val F'.val F.prop F'.prop
  exact ⟨g.val,Subtype.ext hg⟩

theorem gaussianImage_eq_self_iff (g : gaussianLatticeGroup) (F : Set MinimalCross) :
    gaussianImage g F=F ↔ ∀c : MinimalCross,c∈F ↔ g • c∈F := by
  constructor
  · intro h c
    have hm := gaussianImage_mem g F c
    rw [h] at hm
    exact hm.symm
  · intro h
    ext c
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (h z).mp hz
    · intro hc
      refine ⟨g⁻¹ • c,?_,smul_inv_smul g c⟩
      apply (h (g⁻¹ • c)).mpr
      simpa only [smul_inv_smul] using hc

theorem canonicalFrame_stabilizer_eq :
    MulAction.stabilizer gaussianLatticeGroup referenceCanonicalFrame=gaussianCoordinateFrameStabilizer := by
  ext g
  change (g • referenceCanonicalFrame=referenceCanonicalFrame) ↔ _
  rw [Subtype.ext_iff]
  exact gaussianImage_eq_self_iff g coordinateFrame

theorem canonicalFrame_stabilizer_order :
    Nat.card (MulAction.stabilizer gaussianLatticeGroup referenceCanonicalFrame)=1376256 := by
  rw [canonicalFrame_stabilizer_eq,gaussianCoordinateFrameStabilizer_order]

theorem canonicalFrame_full_orbit_card :
    Nat.card (MulAction.orbit gaussianLatticeGroup referenceCanonicalFrame)=Nat.card canonicalBases := by
  let := canonicalFrames_gaussian_pretransitive
  rw [MulAction.orbit_eq_univ,Nat.card_univ]

/-- Orbit–stabilizer for the actual full Gaussian lattice group and intrinsic frames. -/
theorem full_gaussian_order_eq_frames_mul :
    Nat.card gaussianLatticeGroup=Nat.card canonicalBases*1376256 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    gaussianLatticeGroup referenceCanonicalFrame)
  rw [Nat.card_prod,canonicalFrame_full_orbit_card,canonicalFrame_stabilizer_order] at h
  exact h.symm

end Atlas.Rudvalis
