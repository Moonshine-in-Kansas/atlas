import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! Cardinality of a finite set with a free finite group action. -/
namespace Atlas

theorem free_action_card (G X : Type*) [Group G] [MulAction G X] [Finite G] [Finite X]
    (hfree : ∀g : G,∀x : X,g • x=x → g=1) :
    Nat.card X=Nat.card (Quotient (MulAction.orbitRel G X))*Nat.card G := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel G X))
  have hs (x : X) : MulAction.stabilizer G x=⊥ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff,Subgroup.mem_bot]
    exact ⟨hfree g x,fun h => by rw [h,one_smul]⟩
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X),Nat.card_sigma]
  simp_rw [hs]
  rw [Nat.card_congr (QuotientGroup.quotientBot (G:=G)).toEquiv]
  simp [Nat.card_eq_fintype_card]

end Atlas
