import Atlas.Mathieu.Mathieu22PairAction
import Atlas.Mathieu.Mathieu22Witt
import Mathlib.Algebra.Group.Action.TransferInstance

noncomputable section
namespace Atlas.Codes
open Finset
set_option synthInstance.maxHeartbeats 200000

instance mathieu22PairOriginalAction (a : Omega) (b : Mathieu23Points a) :
    MulAction (Mathieu22PairModel a b) (Mathieu22Points a b) :=
  (mathieu22PairPointsEquiv a b).symm.mulAction _

theorem mathieu22PairOriginalAction_coordinate (a : Omega) (b : Mathieu23Points a)
    (g : Mathieu22PairModel a b) (x : Mathieu22Points a b) :
    (g • x).val.val = g.val.val x.val.val := rfl

def mathieu22AmbientBlock (a : Omega) (b : Mathieu23Points a)
    (B : Finset (Mathieu22Points a b)) : Finset Omega := by
  classical
  exact insert a (insert b.val (B.image (fun x => x.val.val)))

theorem mathieu22Blocks_mem_ambient (a : Omega) (b : Mathieu23Points a)
    (B : Finset (Mathieu22Points a b)) :
    B ∈ mathieu22Blocks a b ↔ mathieu22AmbientBlock a b B ∈ octads := by
  classical
  rw [mathieu22Blocks_mem]
  have hl : mathieu23BlockLift a (mathieu22BlockLift a b B) =
      B.image (fun x => x.val.val) := by
    let f : Mathieu22Points a b ↪ Mathieu23Points a := ⟨Subtype.val,Subtype.val_injective⟩
    let k : Mathieu23Points a ↪ Omega := ⟨Subtype.val,Subtype.val_injective⟩
    change (B.map f).map k = B.image (fun x => x.val.val)
    rw [Finset.map_map,Finset.map_eq_image]
    rfl
  change insert a ((insert b (mathieu22BlockLift a b B)).map (Function.Embedding.subtype _)) ∈ octads ↔ _
  rw [Finset.map_insert]
  change insert a (insert b.val (mathieu23BlockLift a (mathieu22BlockLift a b B))) ∈ octads ↔ _
  rw [hl]
  rfl

def mathieu22PairPermuteBlock (a : Omega) (b : Mathieu23Points a)
    (g : Mathieu22PairModel a b) (B : Finset (Mathieu22Points a b)) :
    Finset (Mathieu22Points a b) := by
  classical
  exact B.image (fun x => g • x)

theorem mathieu22PairAmbient_permute (a : Omega) (b : Mathieu23Points a)
    (g : Mathieu22PairModel a b) (B : Finset (Mathieu22Points a b)) :
    mathieu22AmbientBlock a b (mathieu22PairPermuteBlock a b g B) =
      permuteBlock g.val.val (mathieu22AmbientBlock a b B) := by
  classical
  have hg := (Atlas.GroupTheory.pairStabilizer_mem a b.val (Ne.symm b.prop) g.val).mp g.prop
  have hl : (mathieu22PairPermuteBlock a b g B).image (fun x => x.val.val) =
      (B.image (fun x => x.val.val)).image g.val.val := by
    simp only [mathieu22PairPermuteBlock,Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact mathieu22PairOriginalAction_coordinate a b g x
  unfold mathieu22AmbientBlock
  rw [hl]
  rcases hg with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · change g.val.val a = a at ha
    change g.val.val b.val = b.val at hb
    simp only [permuteBlock,Finset.image_insert,ha,hb]
  · change g.val.val a = b.val at ha
    change g.val.val b.val = a at hb
    simp only [permuteBlock,Finset.image_insert,ha,hb]
    rw [Finset.insert_comm]

theorem mathieu22PairBlocks_preserved (a : Omega) (b : Mathieu23Points a)
    (g : Mathieu22PairModel a b) (B : Finset (Mathieu22Points a b))
    (hB : B ∈ mathieu22Blocks a b) :
    mathieu22PairPermuteBlock a b g B ∈ mathieu22Blocks a b := by
  rw [mathieu22Blocks_mem_ambient,mathieu22PairAmbient_permute]
  exact codePreserving_octad_forward g.val.val g.val.prop _
    ((mathieu22Blocks_mem_ambient a b B).mp hB)

end Atlas.Codes
