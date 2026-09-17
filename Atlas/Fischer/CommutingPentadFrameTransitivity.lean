import Atlas.Fischer.CommutingPentadFrameCount

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual pointwise stabilizer of every ordered commuting pentad acts
transitively on its three frames, by transporting the actual fixing switches. -/
theorem commutingPentadFrame_transitive (t : OrderedCommutingTuple 5) :
    MulAction.IsPretransitive (MulAction.stabilizer rootGeneratedRayGroup t)
      (CommutingPentadFrame t) := by
  obtain ⟨a : Fin 5 ↪ Omega⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 5) ≤ Fintype.card Omega by decide)
  let b := basicOrderedCommutingTuple a
  haveI := orderedCommutingTuple_transitive 5 (by omega)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq rootGeneratedRayGroup b t
  let E := commutingPentadFrameTransport g b t hg
  haveI := basicCommutingPentadFrame_transitive a
  constructor
  intro F K
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (MulAction.stabilizer rootGeneratedRayGroup b)
    (E.symm F) (E.symm K)
  have hf : h.val • b=b := MulAction.mem_stabilizer_iff.mp h.prop
  let k : MulAction.stabilizer rootGeneratedRayGroup t := ⟨g*h.val*g⁻¹,by
    rw [MulAction.mem_stabilizer_iff,← hg]
    simp only [mul_smul,inv_smul_smul,hf]⟩
  refine ⟨k,?_⟩
  apply Subtype.ext
  have hh' := congrArg Subtype.val hh
  change h.val • (g⁻¹ • F.val)=g⁻¹ • K.val at hh'
  change (g*h.val*g⁻¹) • F.val=K.val
  calc
    _ = g • (h.val • (g⁻¹ • F.val)) := by rw [mul_smul,mul_smul]
    _ = K.val := by rw [hh',smul_inv_smul]

end Atlas.Fischer
