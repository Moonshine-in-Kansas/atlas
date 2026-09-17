import Atlas.Mathieu.Mathieu22PairStabilizer
import Atlas.Mathieu.Mathieu24Alternating
import Atlas.GroupTheory.EvenPairComplement

noncomputable section
namespace Atlas.Codes
open scoped Pointwise

abbrev Mathieu22PairPoints (a : Omega) (b : Mathieu23Points a) :=
  ({a,b.val} : Set Omega)ᶜ

def mathieu22PairComplementHom (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PairModel a b →* MulAction.stabilizer Mathieu24CodeModel (Mathieu22PairPoints a b) :=
  Subgroup.inclusion (by rw [stabilizer_compl])

instance mathieu22PairMulAction (a : Omega) (b : Mathieu23Points a) :
    MulAction (Mathieu22PairModel a b) (Mathieu22PairPoints a b) :=
  MulAction.compHom _ (mathieu22PairComplementHom a b)

def mathieu22PairPointsEquiv (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PairPoints a b ≃ Mathieu22Points a b where
  toFun x := ⟨⟨x.val,fun h => x.prop (Or.inl h)⟩,
    fun h => x.prop (Or.inr (congrArg Subtype.val h))⟩
  invFun x := ⟨x.val.val,by
    rintro (h | h)
    · exact x.val.prop h
    · exact x.prop (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mathieu22Pair_degree (a : Omega) (b : Mathieu23Points a) :
    Nat.card (Mathieu22PairPoints a b) = 22 :=
  (Nat.card_congr (mathieu22PairPointsEquiv a b)).trans (mathieu22_degree a b)

theorem mathieu22Pair_faithful (a : Omega) (b : Mathieu23Points a) :
    FaithfulSMul (Mathieu22PairModel a b) (Mathieu22PairPoints a b) := by
  constructor
  intro g h he
  have hz : (g⁻¹*h).val.val = 1 := by
    apply Atlas.GroupTheory.even_fixed_outside_pair a b.val _ (mathieu24_even _)
    intro x hxa hxb
    let y : Mathieu22PairPoints a b := ⟨x,by rintro (ha | hb); exact hxa ha; exact hxb hb⟩
    have hh : (g⁻¹*h) • y = y := by rw [mul_smul,← he y,inv_smul_smul]
    exact congrArg Subtype.val hh
  have hgh : g⁻¹*h = 1 := Subtype.ext (Subtype.ext hz)
  exact inv_mul_eq_one.mp hgh

end Atlas.Codes
