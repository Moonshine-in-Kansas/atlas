import Atlas.Rudvalis.FourPlaneShortening
import Atlas.Rudvalis.HeavyLiftCount
import Atlas.Rudvalis.MinimumAction

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

def fourPlaneSeedResidue : BinaryWord := fourPlaneSupport ![0,0,0,1]
def fourSeedResidue : BinaryWord := binaryNormalMap seedAParameters

theorem fourPlaneSeedResidue_parameters : fourPlaneSeedResidue=
    binaryNormalMap (seedEncodedParameters 149) := by
  funext z
  decide +kernel +revert

theorem fourthSeed_residue : reduce (quaternarySeed (3,0,0,0))=fourPlaneSeedResidue := by
  have h := seedOrbitResidue_parameters 48
  change seedOrbitResidue (3,0,0,0)=_ at h
  rw [fourPlaneSeedResidue_parameters]
  rw [quaternarySeed_reduce]
  exact h

theorem codeP_cube_seedA : monomialHom (codeP^3).val (quaternarySeed (0,0,0,0))=
    quaternarySeed (3,0,0,0) := by
  have h (t : SeedOrbitIndex) : monomialHom codeP.val (quaternarySeed t)=
      quaternarySeed (seedNextRow t.1,t.2) := rudvalisPMonomial_seed t
  change monomialHom (codeP.val^3) (quaternarySeed (0,0,0,0))=_
  rw [pow_succ,pow_succ,pow_succ,pow_zero]
  simp only [map_mul,map_one,LinearEquiv.mul_apply]
  change monomialHom codeP.val (monomialHom codeP.val (monomialHom codeP.val (quaternarySeed (0,0,0,0))))=_
  rw [h,h,h]
  rfl

theorem fourthSeed_weight : euclideanWeight (quaternarySeed (3,0,0,0))=16 := by
  rw [← codeP_cube_seedA]
  exact (monomial_euclideanWeight _ _).trans (quaternary_base_seed_weight 0)

noncomputable def fourPlaneSeedMinimumLift : minimumLift fourPlaneSeedResidue :=
  ⟨⟨quaternarySeed (3,0,0,0),quaternaryCode_seed _⟩,fourthSeed_weight,fourthSeed_residue⟩

theorem fourPlaneSeedResidue_weight : hammingNorm fourPlaneSeedResidue=16 := by
  rw [← fourthSeed_residue]
  exact quaternary_minimum_residue_weight _ (quaternaryCode_seed _) fourthSeed_weight

theorem fourPlaneSeed_minimum_lifts_card : Nat.card (minimumLift fourPlaneSeedResidue)=32 := by
  rw [minimumLift_card _ fourPlaneSeedResidue_weight fourPlaneSeedMinimumLift]
  exact fourPlaneShortCode_card ![0,0,0,1] (by decide +kernel)

noncomputable def fourSeedMinimumLift : minimumLift fourSeedResidue :=
  ⟨⟨quaternarySeed (0,0,0,0),quaternaryCode_seed _⟩,quaternary_base_seed_weight 0,by
    rw [quaternarySeed_reduce]
    exact seedA_residue⟩

theorem fourSeedResidue_weight : hammingNorm fourSeedResidue=16 := by
  rw [← fourSeedMinimumLift.prop.2]
  exact quaternary_minimum_residue_weight _ fourSeedMinimumLift.val.prop fourSeedMinimumLift.prop.1

theorem fourSeed_minimum_lifts_card : Nat.card (minimumLift fourSeedResidue)=32 := by
  have hd : fourPlaneSeedResidue=fourSeedResidue ∘ (codeP^3).val.right.symm := by
    have h := congrArg reduce codeP_cube_seedA
    rw [fourthSeed_residue] at h
    change reduce (monomialAction (codeP^3).val (quaternarySeed (0,0,0,0)))=_ at h
    rw [monomialAction_reduce] at h
    have ha : reduce (quaternarySeed (0,0,0,0))=fourSeedResidue := fourSeedMinimumLift.prop.2
    rw [ha] at h
    exact h.symm
  have hc := minimumLift_card_binary_transport (codePermutationHom (codeP^3)) fourSeedResidue fourSeedResidue_weight
  change Nat.card (minimumLift (fourSeedResidue ∘ (codeP^3).val.right.symm))=_ at hc
  rw [← hd,fourPlaneSeed_minimum_lifts_card] at hc
  exact hc.symm

end Atlas.Rudvalis
