import Atlas.Rudvalis.BinaryBlocks

/-! A six-coordinate word attaining the proved torsion lower bound. -/
namespace Atlas.Rudvalis

def torsionSixWord : BinaryWord := fun z =>
  if (z.1.val = binaryLabel 1 ∨ z.1.val = binaryLabel 2 ∨ z.1.val = binaryLabel 3) ∧
    (z.2 = binaryLabel 0 ∨ z.2 = binaryLabel 4) then 1 else 0

theorem torsionSixWord_weight : hammingNorm torsionSixWord = 6 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 500000 in
-- Kernel reduction checks 19 pairings, each on the 56 actual coordinates.
theorem torsionSixWord_generator_pairing (i : BinaryGeneratorIndex) :
    Atlas.Codes.binaryDot (binaryNormalMap (binaryParameterGenerator i)) torsionSixWord = 0 := by
  decide +kernel +revert

theorem torsionSixWord_mem : torsionSixWord ∈ binaryTorsion := by
  rintro w ⟨a,rfl⟩
  rw [binaryNormalMap_expansion a]
  simp [map_sum,map_smul,torsionSixWord_generator_pairing]

theorem binaryTorsion_minimum_attained :
    (∀ w ∈ binaryTorsion, w ≠ 0 → 6 ≤ hammingNorm w) ∧
      ∃ w ∈ binaryTorsion, hammingNorm w = 6 :=
  ⟨binaryTorsion_minimum, torsionSixWord, torsionSixWord_mem, torsionSixWord_weight⟩

end Atlas.Rudvalis
