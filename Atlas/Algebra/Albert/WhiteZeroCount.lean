import Atlas.Algebra.Albert.WhiteConeCount

noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F] [Finite F]

theorem card_whiteZeroVectors : Nat.card (WhiteZeroVectors F) =
    (Nat.card F^12-1)*(Nat.card F^4+1) := by
  classical
  letI := Fintype.ofFinite F
  have h0 : adjoint (0 : Carrier F)=0 := by
    simpa using adjoint_smul (0 : F) (unit : Carrier F)
  letI : Unique {x : {v : Carrier F // adjoint v=0 ∧ trace v=0} // x.val=0} :=
    { default := ⟨⟨0,h0,by simp [trace]⟩,rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext x.prop) }
  have hz : Fintype.card {x : {v : Carrier F // adjoint v=0 ∧ trace v=0} // x.val=0} = 1 :=
    Fintype.card_unique
  let e : WhiteZeroVectors F ≃
      {x : {v : Carrier F // adjoint v=0 ∧ trace v=0} // x.val≠0} :=
    (Equiv.subtypeEquivRight (fun x => by dsimp [IsRankOne]; tauto)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : Carrier F => adjoint x=0 ∧ trace x=0)
        (fun x => x≠0)).symm
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hz,
    ←Nat.card_eq_fintype_card,card_white_cone]
  omega

end Atlas.Albert
