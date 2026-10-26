import Atlas.Rudvalis.Hamming

namespace Atlas.Rudvalis
open scoped BigOperators

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks 361 generator pairings, each over 56 coordinates.
/-- The small 19 by 19 Gram certificate of the explicit binary generators. -/
theorem binaryGenerator_orthogonal (i j : BinaryGeneratorIndex) :
    Atlas.Codes.binaryDot (binaryNormalMap (binaryParameterGenerator i))
      (binaryNormalMap (binaryParameterGenerator j)) = 0 := by
  decide +kernel +revert

theorem binaryNormalMap_orthogonal (a b : BinaryParameters) :
    Atlas.Codes.binaryDot (binaryNormalMap a) (binaryNormalMap b) = 0 := by
  rw [binaryNormalMap_expansion a, binaryNormalMap_expansion b]
  simp [map_sum, map_smul, binaryGenerator_orthogonal]

theorem binaryResidue_self_orthogonal : binaryResidue ≤ binaryTorsion := by
  rintro u ⟨a,rfl⟩ v ⟨b,rfl⟩
  exact binaryNormalMap_orthogonal b a

end Atlas.Rudvalis
