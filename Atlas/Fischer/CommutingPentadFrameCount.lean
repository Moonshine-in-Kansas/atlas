import Atlas.Fischer.CommutingPentadFrameTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The standard tuple incidence is exactly the retained marked-subset incidence. -/
def commutingPentadMarkedEquiv (a : Fin 5 ↪ Omega) :
    CommutingPentadFrame (basicOrderedCommutingTuple a) ≃
      MarkedPentadFrame (Finset.univ.image a) where
  toFun F := ⟨F.val.val,F.val.prop,by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact F.prop k⟩
  invFun F := ⟨⟨F.val,F.prop.1⟩,fun k =>
    F.prop.2 (a k) (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every actual ordered commuting pentad lies in exactly three actual frames. -/
theorem commutingPentadFrame_card (t : OrderedCommutingTuple 5) :
    Nat.card (CommutingPentadFrame t)=3 := by
  obtain ⟨a : Fin 5 ↪ Omega⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 5) ≤ Fintype.card Omega by decide)
  haveI := orderedCommutingTuple_transitive 5 (by omega)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq rootGeneratedRayGroup (basicOrderedCommutingTuple a) t
  rw [← Nat.card_congr (commutingPentadFrameTransport g _ _ hg),
    Nat.card_congr (commutingPentadMarkedEquiv a)]
  apply markedPentadFrame_card
  rw [Finset.card_image_of_injective _ a.injective,Finset.card_univ,Fintype.card_fin]

theorem basicCommutingPentadFrame_transitive (a : Fin 5 ↪ Omega) :
    MulAction.IsPretransitive
      (MulAction.stabilizer rootGeneratedRayGroup (basicOrderedCommutingTuple a))
      (CommutingPentadFrame (basicOrderedCommutingTuple a)) := by
  haveI := markedPentadFrame_transitive (Finset.univ.image a) (by
    rw [Finset.card_image_of_injective _ a.injective,Finset.card_univ,Fintype.card_fin])
  constructor
  intro F K
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (markedPentadPointwise (Finset.univ.image a))
    (commutingPentadMarkedEquiv a F) (commutingPentadMarkedEquiv a K)
  let g : MulAction.stabilizer rootGeneratedRayGroup (basicOrderedCommutingTuple a) :=
    ⟨h.val,by rw [basicOrderedCommutingTuple_stabilizer];exact h.prop⟩
  refine ⟨g,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hh' := congrArg (fun Z : MarkedPentadFrame (Finset.univ.image a) => Z.val) hh
  exact hh'

end Atlas.Fischer
