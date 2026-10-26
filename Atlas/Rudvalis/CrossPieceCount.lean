import Atlas.Rudvalis.LatticeCrossPartition
import Mathlib.Logic.Equiv.Sum

namespace Atlas.Rudvalis

noncomputable def crossPieceMap : CoordinateCrosses ⊕ FourBlockCrosses ⊕ HeavyCrosses → MinimalCross :=
  Sum.elim (shellPieceCrossMap coordinateShellPiece)
    (Sum.elim (shellPieceCrossMap fourShellPiece) (shellPieceCrossMap heavyShellPiece))

theorem crossPieceMap_bijective : Function.Bijective crossPieceMap := by
  constructor
  · intro a b h
    rcases a with a|a|a <;> rcases b with b|b|b
    · exact congrArg Sum.inl (shellPieceCrossMap_injective _ h)
    · exact (coordinate_four_cross_disjoint a b h).elim
    · exact (coordinate_heavy_cross_disjoint a b h).elim
    · exact (coordinate_four_cross_disjoint b a h.symm).elim
    · exact congrArg (Sum.inr ∘ Sum.inl) (shellPieceCrossMap_injective _ h)
    · exact (four_heavy_cross_disjoint a b h).elim
    · exact (coordinate_heavy_cross_disjoint b a h.symm).elim
    · exact (four_heavy_cross_disjoint b a h.symm).elim
    · exact congrArg (Sum.inr ∘ Sum.inr) (shellPieceCrossMap_injective _ h)
  · intro c
    rcases minimalCross_piece_cases c with ⟨a,ha⟩|⟨a,ha⟩|⟨a,ha⟩
    · exact ⟨Sum.inl a,ha⟩
    · exact ⟨Sum.inr (Sum.inl a),ha⟩
    · exact ⟨Sum.inr (Sum.inr a),ha⟩

noncomputable def crossPieceEquiv : CoordinateCrosses ⊕ FourBlockCrosses ⊕ HeavyCrosses ≃ MinimalCross :=
  Equiv.ofBijective crossPieceMap crossPieceMap_bijective

noncomputable def crossPieceConditionEquiv (P : MinimalCross→Prop) :
    {c : MinimalCross // P c} ≃
      {c : CoordinateCrosses // P (shellPieceCrossMap coordinateShellPiece c)} ⊕
      {c : FourBlockCrosses // P (shellPieceCrossMap fourShellPiece c)} ⊕
      {c : HeavyCrosses // P (shellPieceCrossMap heavyShellPiece c)} :=
  (Equiv.subtypeEquiv crossPieceEquiv (fun _ => Iff.rfl)).symm.trans
    (Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _) Equiv.subtypeSum))

theorem crossPiece_condition_card (P : MinimalCross→Prop) :
    Nat.card {c : MinimalCross // P c}=
      Nat.card {c : CoordinateCrosses // P (shellPieceCrossMap coordinateShellPiece c)}+
      (Nat.card {c : FourBlockCrosses // P (shellPieceCrossMap fourShellPiece c)}+
      Nat.card {c : HeavyCrosses // P (shellPieceCrossMap heavyShellPiece c)}) := by
  rw [Nat.card_congr (crossPieceConditionEquiv P),Nat.card_sum,Nat.card_sum]

end Atlas.Rudvalis
