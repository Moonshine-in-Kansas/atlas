import Atlas.Codes.TernaryHexadProjection

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

abbrev TernaryHexadAffinePhase (c : TernarySixWords) (e : ZMod 3) :=
  {a : ternarySupport c.val.val → ZMod 3 // ternaryHexadFunctional c a=e}

def ternaryHexadAffinePhaseEquiv (c : TernarySixWords) (e : ZMod 3) :
    TernaryHexadAffinePhase c e ≃ (ternaryHexadFunctional c).ker := by
  let a := Classical.choose (ternaryHexadFunctional_surjective c e)
  have ha := Classical.choose_spec (ternaryHexadFunctional_surjective c e)
  exact {
    toFun := fun x => ⟨x.val-a,by rw [LinearMap.mem_ker,map_sub,x.prop,ha,sub_self]⟩
    invFun := fun x => ⟨x.val+a,by rw [map_add,(LinearMap.mem_ker.mp x.prop),ha,zero_add]⟩
    left_inv := fun x => Subtype.ext (sub_add_cancel x.val a)
    right_inv := fun x => Subtype.ext (add_sub_cancel_right x.val a)
  }

theorem ternaryHexadAffinePhase_card (c : TernarySixWords) (e : ZMod 3) :
    Nat.card (TernaryHexadAffinePhase c e)=243 := by
  rw [Nat.card_congr (ternaryHexadAffinePhaseEquiv c e)]
  exact ternaryHexadPhase_card c

end Atlas.Codes
