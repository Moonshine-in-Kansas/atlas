import Atlas.Tits.TransferTwoCycleCancellation
import Atlas.Tits.TransferFixedCharacters

namespace Atlas.Tits
open Atlas.GroupTheory
open scoped BigOperators

theorem geometricCycleLength_eq_period (O : GeometricCycles localAlpha) :
    Nat.card O.orbit = Function.minimalPeriod (localAlpha • ·) O.out := by
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq',
    card_zpowers_orbit_eq_minimalPeriod]

theorem alpha_cycle_length_cases (O : GeometricCycles localAlpha) :
    Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 := by
  rw [geometricCycleLength_eq_period]
  exact localAlpha_period_cases O.out

theorem alpha_one_cycle_value (O : GeometricCycles localAlpha)
    (hO : Nat.card O.orbit = 1) : geometricCycleValue localAlpha O = -1 := by
  rw [geometricCycleLength_eq_period] at hO
  rw [geometricCycleValue_out]
  unfold pointCycleValue
  simp only [hO,pow_one]
  exact multiplierAt_alpha_fixed O.out _

theorem alpha_four_cycle_value (O : GeometricCycles localAlpha)
    (hO : Nat.card O.orbit = 4) : geometricCycleValue localAlpha O = 1 := by
  rw [geometricCycleLength_eq_period] at hO
  rw [geometricCycleValue_out]
  unfold pointCycleValue
  simp only [hO,localAlpha_fourth]
  exact map_one _

open scoped Classical in
/-- Three fixed points each contribute the multiplier -1. -/
theorem alpha_one_cycle_product :
    ∏ O : CyclesOfLength localAlpha Neighbours 1,
      geometricCycleValue localAlpha O.val = -1 := by
  classical
  have h : ∀ O : CyclesOfLength localAlpha Neighbours 1,
      geometricCycleValue localAlpha O.val = -1 := fun O => alpha_one_cycle_value O.val O.prop
  simp only [h,Finset.prod_const,Finset.card_univ,←Nat.card_eq_fintype_card,
    localAlpha_one_cycles_card]
  decide

open scoped Classical in
theorem alpha_nonfixed_cycle_product :
    ∏ O : {O : GeometricCycles localAlpha // Nat.card O.orbit ≠ 1},
      geometricCycleValue localAlpha O.val = 1 := by
  classical
  let e : AlphaTwoCycles → {O : GeometricCycles localAlpha // Nat.card O.orbit ≠ 1} :=
    fun O => ⟨O.val,by rw [O.prop]; decide⟩
  have he : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun O : {O : GeometricCycles localAlpha // Nat.card O.orbit ≠ 1} => O.val) h
  have hp := Fintype.prod_of_injective e he
    (fun O => geometricCycleValue localAlpha O.val)
    (fun O => geometricCycleValue localAlpha O.val) (by
      intro O ho
      have hn : Nat.card O.val.orbit ≠ 2 := by
        intro h
        exact ho ⟨⟨O.val,h⟩,Subtype.ext rfl⟩
      rcases alpha_cycle_length_cases O.val with h | h | h
      · exact False.elim (O.prop h)
      · exact False.elim (hn h)
      · exact alpha_four_cycle_value O.val h) (fun _ => rfl)
  rw [←hp]
  exact alpha_two_cycle_product

/-- The actual transfer takes alpha=qW to -1; no target-group assumption occurs. -/
theorem transfer_alpha : transfer localAlpha = -1 := by
  classical
  rw [transfer_geometric_cycle_product]
  rw [←Fintype.prod_subtype_mul_prod_subtype
    (fun O : GeometricCycles localAlpha => Nat.card O.orbit = 1)]
  rw [alpha_one_cycle_product,alpha_nonfixed_cycle_product,mul_one]

end Atlas.Tits
