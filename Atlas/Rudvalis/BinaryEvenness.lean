import Atlas.Rudvalis.BinaryOrthogonality
import Atlas.Codes.BinaryWeight

/-! Double evenness of the Version 33 binary residue code. -/
namespace Atlas.Rudvalis
open scoped BigOperators

/-- A finite certificate for the weights of the nineteen spanning words. -/
theorem binaryGenerator_doubly_even (i : BinaryGeneratorIndex) :
    4 ∣ hammingNorm (binaryNormalMap (binaryParameterGenerator i)) := by
  decide +kernel +revert

theorem binaryResidue_doubly_even (w : BinaryWord) (hw : w ∈ binaryResidue) :
    4 ∣ hammingNorm w := by
  classical
  obtain ⟨a,rfl⟩ := hw
  rw [binaryNormalMap_expansion]
  have hg (i : BinaryGeneratorIndex) :
      binaryParameterCoefficient a i • binaryNormalMap (binaryParameterGenerator i) ∈ binaryResidue ∧
      4 ∣ hammingNorm (binaryParameterCoefficient a i •
        binaryNormalMap (binaryParameterGenerator i)) := by
    constructor
    · exact binaryResidue.smul_mem _ ⟨binaryParameterGenerator i,rfl⟩
    · rcases Atlas.Codes.bit_cases (binaryParameterCoefficient a i) with h | h
      · simp [h]
      · simpa [h] using binaryGenerator_doubly_even i
  have hs (s : Finset BinaryGeneratorIndex) :
      (∑ i ∈ s, binaryParameterCoefficient a i • binaryNormalMap (binaryParameterGenerator i)) ∈
        binaryResidue ∧
      4 ∣ hammingNorm (∑ i ∈ s, binaryParameterCoefficient a i •
        binaryNormalMap (binaryParameterGenerator i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine ⟨binaryResidue.add_mem (hg i).1 ih.1, ?_⟩
      exact Atlas.Codes.doublyEven_add _ _ (hg i).2 ih.2
        (binaryResidue_self_orthogonal ih.1 _ (hg i).1)
  exact (hs Finset.univ).2

theorem binaryResidue_one : (fun _ : Coordinate => (1 : Bit)) ∈ binaryResidue := by
  refine ⟨(fun _ => 1,0,0), ?_⟩
  funext z
  simp [binaryNormalMap, matrixAt, theta, quadratic, dot, eta]

theorem binaryTorsion_even (w : BinaryWord) (hw : w ∈ binaryTorsion) :
    Even (hammingNorm w) := by
  have h := hw (fun _ => 1) binaryResidue_one
  rw [Atlas.Codes.binaryDot_overlap] at h
  have ho : Atlas.Codes.overlap (fun _ : Coordinate => 1) w = hammingNorm w := by
    simp [Atlas.Codes.overlap, hammingNorm]
  rw [ho, ZMod.natCast_eq_zero_iff_even] at h
  exact h

end Atlas.Rudvalis
