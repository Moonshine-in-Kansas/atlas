import Atlas.Fischer.ResidueElementaryCocode
import Atlas.Fischer.ResidueCentralizerOrder
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The central quotient of the actual marked centralizer. -/
abbrev ResidueGroup (S : Finset Omega) := residueCentralizer S ⧸ residueCentralElementary S

def residueCocodeSpanEquiv (S : Finset Omega) :
    residueCocodeSubgroup S ≃ coordinateCocodeSpan S where
  toFun x := ⟨x.val.toAdd,x.property⟩
  invFun x := ⟨Multiplicative.ofAdd x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem residueElementary_card (S : Finset Omega) (hS : S.card<8) :
    Nat.card (residueElementary S) = 2^S.card := by
  rw [residueElementary_eq_cocode_image,
    ← Nat.card_congr ((residueCocodeSubgroup S).equivMapOfInjective generatedCocodeRayHom
      (fun x y h => cocodeRayHom_injective (congrArg Subtype.val h))).toEquiv,
    Nat.card_congr (residueCocodeSpanEquiv S),coordinateCocodeSpan_card S hS]

theorem residueCentralElementary_card (S : Finset Omega) (hS : S.card<8) :
    Nat.card (residueCentralElementary S) = 2^S.card := by
  unfold residueCentralElementary
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (residueElementary_le_centralizer S)).toEquiv]
  exact residueElementary_card S hS

theorem residueGroup_order_product (S : Finset Omega) (hS : S.card<8) :
    Nat.card (ResidueGroup S) * 2^S.card = Nat.card (residueCentralizer S) := by
  rw [← residueCentralElementary_card S hS]
  exact (residueCentralElementary S).index_mul_card


/-- Exact residue order at one marked involution. -/
theorem residueGroup_singleton_order (S : Finset Omega) (hS : S.card = 1) :
    Nat.card (ResidueGroup S) = 4089470473293004800 := by
  have h := residueGroup_order_product S (by omega)
  rw [hS,markedCentralizer_singleton_order S hS] at h
  norm_num at h
  omega

/-- Exact residue order at two distinct commuting marked involutions. -/
theorem residueGroup_pair_order (S : Finset Omega) (hS : S.card = 2) :
    Nat.card (ResidueGroup S) = 64561751654400 := by
  have h := residueGroup_order_product S (by omega)
  rw [hS,markedCentralizer_pair_order S hS] at h
  norm_num at h
  omega

theorem residueGroup_singleton_order_identity (S : Finset Omega) (hS : S.card = 1) :
    2 * 306936 * Nat.card (ResidueGroup S) = Nat.card rootGeneratedRayGroup := by
  rw [residueGroup_singleton_order S hS,rootGeneratedRayGroup_order_value]

theorem residueGroup_pair_order_identity (S : Finset Omega) (hS : S.card = 2) :
    4 * 306936 * 31671 * Nat.card (ResidueGroup S) = Nat.card rootGeneratedRayGroup := by
  rw [residueGroup_pair_order S hS,rootGeneratedRayGroup_order_value]

end Atlas.Fischer

