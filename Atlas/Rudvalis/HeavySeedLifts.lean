import Atlas.Rudvalis.HeavyShortening
import Atlas.Rudvalis.MinimumLiftFibres

/-! Exactly sixteen minimum lifts of the literal heavy seed residue. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def heavySeedMinimumLift : minimumLift heavySeedResidue :=
  ⟨⟨quaternarySeed (0,0,0,1),quaternaryCode_seed _⟩,quaternary_base_seed_weight 1,by
    rw [quaternarySeed_reduce]
    rfl⟩

theorem heavySeed_minimum_lifts_card : Nat.card (minimumLift heavySeedResidue)=16 := by
  have hd : hammingNorm heavySeedResidue=16 := by
    rw [← heavySeedMinimumLift.prop.2]
    exact quaternary_minimum_residue_weight _ heavySeedMinimumLift.val.prop heavySeedMinimumLift.prop.1
  rw [minimumLift_card heavySeedResidue hd heavySeedMinimumLift]
  exact heavyShortCode_card

end Atlas.Rudvalis
