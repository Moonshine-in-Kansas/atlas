import Atlas.Rudvalis.FourLiftCount

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem four_heavy_disjoint (d : BinaryWord) (hd : admissibleFourSupport d) :
    ¬hasNonzeroQuadraticPart d := by
  obtain ⟨a,ε,rfl,_,_⟩ := hd
  rw [hasNonzeroQuadraticPart_normal_iff]
  simp

noncomputable def minimumWordsSplit : MinimumWords ≃ FourMinimumWords ⊕ HeavyMinimumWords := by
  classical
  exact {
    toFun := fun w => if h : admissibleFourSupport (reduce w.val.val) then
      Sum.inl ⟨w.val,w.prop,h⟩ else
      Sum.inr ⟨w.val,w.prop,(quaternary_minimum_support_cases _ w.val.prop w.prop).resolve_left h⟩
    invFun := fun w => w.elim (fun v => ⟨v.val,v.prop.1⟩) (fun v => ⟨v.val,v.prop.1⟩)
    left_inv := fun w => by dsimp; split <;> rfl
    right_inv := fun w => by
      cases w with
      | inl v => simp [v.prop.2]
      | inr v =>
        have hn : ¬admissibleFourSupport (reduce v.val.val) := fun h => four_heavy_disjoint _ h v.prop.2
        simp [hn] }

theorem quaternary_minimum_words_card : Nat.card MinimumWords=16128 := by
  rw [Nat.card_congr minimumWordsSplit,Nat.card_sum,four_minimum_words_card,
    heavy_minimum_words_card]

end Atlas.Rudvalis
