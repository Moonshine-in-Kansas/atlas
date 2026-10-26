import Atlas.Rudvalis.SignPatterns

/-! The three row moments governing the sign kernel. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def signGenerator (i : Fin 19) : BinaryWord :=
  binaryNormalMap (binaryParameterGenerator (seedGeneratorIndex i))

def generatorBlockGram (i j : Fin 19) (p : Point) : Bit :=
  ∑ x : E, signGenerator i (p,x)*signGenerator j (p,x)

def generatorGramVector (i j : Fin 19) : E :=
  fun k => generatorBlockGram i j (basisPoint k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
-- A19-generator bilinear certificate, not enumeration of the binary code.
theorem generatorBlockGram_linear (i j : Fin 19) (p : Point) :
    generatorBlockGram i j p=dot (generatorGramVector i j) p.val := by
  obtain ⟨r,rfl⟩ := rowEquiv.surjective p
  change generatorBlockGram i j (rowLabel r)=dot (generatorGramVector i j) (rowLabel r).val
  decide +kernel +revert

theorem generatorBlockGram_coordinate (k : Fin 3) (p : Point) :
    generatorBlockGram ⟨7+k.val,by omega⟩ 16 p=p.val k := by
  obtain ⟨r,rfl⟩ := rowEquiv.surjective p
  change generatorBlockGram ⟨7+k.val,by omega⟩ 16 (rowLabel r)=(rowLabel r).val k
  decide +kernel +revert

end Atlas.Rudvalis
