import Atlas.Rudvalis.HeavyOrthogonalTranslations

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def heavyAvoidingIncidenceEquiv (c p : Point) :
    (Σ v : FixedHeavyParameters c,{x : E // fixedHeavyWord c v (p,x)=0 ∧ fixedHeavyWord c v (p,x+p.val)=0}) ≃
      Σ x : E,HeavyAvoidingPair c p x where
  toFun z := ⟨z.2.val,⟨z.1,z.2.prop⟩⟩
  invFun z := ⟨z.2.val,⟨z.1,z.2.prop⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem heavyAvoidingPair_card (c p : Point) (x : E) :
    Nat.card (HeavyAvoidingPair c p x)=if p=c then 0 else 64 := by
  classical
  have hrow (v : FixedHeavyParameters c) :
      Nat.card {y : E // fixedHeavyWord c v (p,y)=0 ∧ fixedHeavyWord c v (p,y+p.val)=0}=
        if p=c then 0 else 4 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact fixedHeavy_row_pairs_card c p v
  have hpos (y : E) : Nat.card (HeavyAvoidingPair c p y)=Nat.card (HeavyAvoidingPair c p 0) :=
    (Nat.card_congr (heavyAvoidingPairEquiv c p y)).symm
  have hh := Nat.card_congr (heavyAvoidingIncidenceEquiv c p)
  rw [Nat.card_sigma,Nat.card_sigma] at hh
  simp_rw [hrow,hpos] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  rw [←Nat.card_eq_fintype_card,fixedHeavyParameters_card] at hh
  have he : Fintype.card E=8 := by decide
  rw [he] at hh
  rw [hpos]
  split_ifs at hh ⊢ <;> omega

end Atlas.Rudvalis
