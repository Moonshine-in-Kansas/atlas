import Atlas.Mathieu.Mathieu11Choice
import Atlas.Mathieu.Mathieu11Witt

noncomputable section
namespace Atlas.Codes

theorem mathieu11ChoiceBlockLift {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val)
    (B : Finset (Mathieu11Points D a)) :
    mathieu11BlockLift E b (B.map (mathieu11ChoicePoints hg ha).toEmbedding) =
      (mathieu11BlockLift D a B).map (mathieu12ChoicePoints hg).toEmbedding := by
  change (B.map (mathieu11ChoicePoints hg ha).toEmbedding).map (Function.Embedding.subtype _) =
    (B.map (Function.Embedding.subtype _)).map (mathieu12ChoicePoints hg).toEmbedding
  rw [Finset.map_map,Finset.map_map]
  rfl

theorem mathieu11Choice_blocks {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val)
    (B : Finset (Mathieu11Points D a)) (hB : B ∈ mathieu11Blocks D a) :
    B.map (mathieu11ChoicePoints hg ha).toEmbedding ∈ mathieu11Blocks E b := by
  classical
  apply (mathieu11Blocks_mem E b _).mpr
  have hH := mathieu12Choice_blocks hg (insert a (mathieu11BlockLift D a B))
    ((mathieu11Blocks_mem D a B).mp hB)
  have hab : mathieu12ChoicePoints hg a = b := Subtype.ext ha
  rw [Finset.map_insert] at hH
  change insert (mathieu12ChoicePoints hg a)
    ((mathieu11BlockLift D a B).map (mathieu12ChoicePoints hg).toEmbedding) ∈ _ at hH
  rw [hab,← mathieu11ChoiceBlockLift hg ha] at hH
  exact hH

end Atlas.Codes
