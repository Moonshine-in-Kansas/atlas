import Atlas.Mathieu.TernaryMathieu11Action
import Atlas.Codes.TernaryGolayAutomorphisms

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Atlas.Codes

def ternaryMathieu11ToPure : TernaryMathieu11 →* TernaryPureAutomorphism where
  toFun g := ⟨ternaryMathieu11Hom g, ternaryMathieu11_preserves g⟩
  map_one' := Subtype.ext (map_one ternaryMathieu11Hom)
  map_mul' g h := Subtype.ext (map_mul ternaryMathieu11Hom g h)

theorem ternaryMathieu11ToPure_injective : Function.Injective ternaryMathieu11ToPure := by
  intro g h he
  exact ternaryMathieu11Hom_injective (congrArg Subtype.val he)

theorem ternaryPureAutomorphism_order : Nat.card TernaryPureAutomorphism = 7920 := by
  have h := Nat.card_le_card_of_injective ternaryMathieu11ToPure ternaryMathieu11ToPure_injective
  rw [ternaryMathieu11_order] at h
  exact Nat.le_antisymm ternaryPureAutomorphism_order_le h

theorem ternaryMathieu11ToPure_bijective : Function.Bijective ternaryMathieu11ToPure := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨ternaryMathieu11ToPure_injective,
    ternaryMathieu11_order.trans ternaryPureAutomorphism_order.symm⟩

/-- The full pure-coordinate group is the existing actual binary-Golay M11,
with its exceptional twelve-coordinate realization. -/
def ternaryPureMathieu11Equiv : TernaryMathieu11 ≃* TernaryPureAutomorphism :=
  MulEquiv.ofBijective ternaryMathieu11ToPure ternaryMathieu11ToPure_bijective

theorem ternaryPureAutomorphism_simple : IsSimpleGroup TernaryPureAutomorphism := by
  letI := ternaryMathieu11_simple
  exact ternaryPureMathieu11Equiv.symm.isSimpleGroup

theorem ternaryPureAutomorphism_three_transitive :
    MulAction.IsMultiplyPretransitive TernaryPureAutomorphism (Fin 12) 3 := by
  have hc : Nat.card (Fin 3 ↪ Fin 12) = 1320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    decide
  have hi : ternaryPureThreeStabilizer.index ≤ 1320 := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact (Nat.card_le_card_of_injective
      (Subtype.val : MulAction.orbit TernaryPureAutomorphism ternaryThreeTuple → (Fin 3 ↪ Fin 12))
      Subtype.val_injective).trans_eq hc
  have he := ternaryPureThreeStabilizer.card_mul_index
  rw [ternaryPureAutomorphism_order] at he
  have hb := Nat.mul_le_mul_right ternaryPureThreeStabilizer.index ternaryPureThree_order_le
  have hn : ternaryPureThreeStabilizer.index = 1320 := by omega
  apply (MulAction.isPretransitive_iff_orbit_eq_univ ternaryThreeTuple).mpr
  apply (Set.eq_univ_iff_ncard _).mpr
  rw [← MulAction.index_stabilizer, hn, hc]

end Atlas.Codes
