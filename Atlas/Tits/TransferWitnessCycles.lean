import Atlas.Tits.TransferSignFixedPoints
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Atlas.GroupTheory.PeriodicOrbitCount

/-! The transfer witness on coordinate rows and the three possible periods
on the full neighbour shell. No enumeration of the shell enters these counts. -/

namespace Atlas.Tits
open Atlas.Rudvalis
set_option maxRecDepth 16384

/-- Seven marked rows determine precisely where the translation fixes a cross. -/
theorem alpha_coordinate_fixed_certificate (p : Point) (x : E) :
    ((p,x+matrixAt alphaTranslationMatrix p.val) = (p,x) ∨
      (p,x+matrixAt alphaTranslationMatrix p.val+p.val) = (p,x)) ↔ p = rowLabel 0 := by
  decide +kernel +revert

theorem codeAlpha_coordinate_fixed_iff (p : Point) (x : E) :
    localCodeAlpha • coordinateCross (p,x) = coordinateCross (p,x) ↔ p = rowLabel 0 := by
  rw [coordinateCross_action]
  have hp := congrArg (fun g : binaryPermutationGroup => g.val (p,x)) localCodeAlpha_translation
  change localCodeAlpha.val.right (p,x) = coordinateTranslation alphaTranslationMatrix (p,x) at hp
  rw [hp,coordinateCross_eq_iff,codeI_coordinate]
  exact alpha_coordinate_fixed_certificate p x

/-- The only fixed neighbours lie in the reference coordinate row. -/
theorem localAlpha_fixed_iff (c : Neighbours) :
    localAlpha • c = c ↔ c.val ∈ coordinateRowFrame (rowLabel 0) := by
  constructor
  · intro hc
    have hs : localAlpha^2 • c = c := by rw [pow_two,mul_smul,hc,hc]
    have hf := (localAlpha_square_fixed_iff c).mp hs
    obtain ⟨⟨p,x⟩,he⟩ := coordinateFrame_rep c.val hf
    have hval := congrArg (fun z : Neighbours => z.val) hc
    change localCodeAlpha • c.val = c.val at hval
    have hfix : localCodeAlpha • coordinateCross (p,x) = coordinateCross (p,x) := by
      rw [he]
      exact hval
    have hp := (codeAlpha_coordinate_fixed_iff p x).mp hfix
    exact ⟨x,by simpa only [hp] using he⟩
  · rintro ⟨x,hx⟩
    apply Subtype.ext
    change localCodeAlpha • c.val = c.val
    rw [← hx]
    exact (codeAlpha_coordinate_fixed_iff (rowLabel 0) x).mpr rfl

noncomputable def alphaFixedEquiv :
    {c : Neighbours // localAlpha • c = c} ≃
      {c : coordinateRowFrame (rowLabel 0) // CrossOrthogonal localReferenceCross c.val} where
  toFun c := ⟨⟨c.val.val,(localAlpha_fixed_iff c.val).mp c.prop⟩,c.val.prop⟩
  invFun c := ⟨⟨c.val.val,c.prop⟩,(localAlpha_fixed_iff _).mpr c.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem localAlpha_fixed_card : Nat.card {c : Neighbours // localAlpha • c = c} = 3 := by
  rw [Nat.card_congr alphaFixedEquiv]
  exact coordinateRowFrame_orthogonal_card (rowLabel 0) ⟨localReferenceCross,by
    refine ⟨0,?_⟩
    exact localReferenceCross_eq.symm⟩

theorem localAlpha_period_cases (c : Neighbours) :
    Function.minimalPeriod (localAlpha • ·) c = 1 ∨
      Function.minimalPeriod (localAlpha • ·) c = 2 ∨
      Function.minimalPeriod (localAlpha • ·) c = 4 := by
  have hd : Function.minimalPeriod (localAlpha • ·) c ∣ 4 :=
    MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp (by rw [localAlpha_fourth,one_smul])
  have hl := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hsmall : ∀ n : Fin 5, n.val ∣ 4 → n.val = 1 ∨ n.val = 2 ∨ n.val = 4 := by decide
  exact hsmall ⟨Function.minimalPeriod (localAlpha • ·) c,Nat.lt_succ_of_le hl⟩ hd

theorem localAlpha_period_one_iff (c : Neighbours) :
    Function.minimalPeriod (localAlpha • ·) c = 1 ↔ localAlpha • c = c := by
  simpa only [pow_one,Nat.dvd_one] using
    (MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := localAlpha) (b := c) (n := 1)).symm

theorem localAlpha_period_two_iff (c : Neighbours) :
    Function.minimalPeriod (localAlpha • ·) c = 2 ↔
      localAlpha^2 • c = c ∧ ¬localAlpha • c = c := by
  rw [MulAction.pow_smul_eq_iff_minimalPeriod_dvd,← localAlpha_period_one_iff]
  rcases localAlpha_period_cases c with h | h | h <;> simp [h]

theorem localAlpha_period_four_iff (c : Neighbours) :
    Function.minimalPeriod (localAlpha • ·) c = 4 ↔ ¬localAlpha^2 • c = c := by
  rw [MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
  rcases localAlpha_period_cases c with h | h | h <;> simp [h]

/-- There are 24 points in two-cycles. -/
theorem localAlpha_period_two_points_card :
    Nat.card {c : Neighbours // Function.minimalPeriod (localAlpha • ·) c = 2} = 24 := by
  have he : {c : Neighbours | Function.minimalPeriod (localAlpha • ·) c = 2} =
      {c : Neighbours | localAlpha^2 • c = c} \ {c : Neighbours | localAlpha • c = c} := by
    ext c
    exact localAlpha_period_two_iff c
  have hsub : {c : Neighbours | localAlpha • c = c} ⊆
      {c : Neighbours | localAlpha^2 • c = c} := by
    intro c hc
    change localAlpha^2 • c = c
    rw [pow_two,mul_smul,hc,hc]
  change Set.ncard {c : Neighbours | Function.minimalPeriod (localAlpha • ·) c = 2} = 24
  rw [he,Set.ncard_sdiff hsub]
  change Nat.card {c : Neighbours // localAlpha^2 • c = c} -
    Nat.card {c : Neighbours // localAlpha • c = c} = 24
  rw [localAlpha_square_fixed_card,localAlpha_fixed_card]

/-- Every other point lies in a four-cycle: there are 1728 such points. -/
theorem localAlpha_period_four_points_card :
    Nat.card {c : Neighbours // Function.minimalPeriod (localAlpha • ·) c = 4} = 1728 := by
  have he : {c : Neighbours | Function.minimalPeriod (localAlpha • ·) c = 4} =
      {c : Neighbours | localAlpha^2 • c = c}ᶜ := by
    ext c
    exact localAlpha_period_four_iff c
  change Set.ncard {c : Neighbours | Function.minimalPeriod (localAlpha • ·) c = 4} = 1728
  rw [he,Set.ncard_compl]
  change Nat.card Neighbours - Nat.card {c : Neighbours // localAlpha^2 • c = c} = 1728
  rw [cardNeighbours,localAlpha_square_fixed_card]

/-- The actual cyclic action has twelve two-cycles. -/
theorem localAlpha_two_cycles_card :
    Nat.card (Atlas.GroupTheory.CyclesOfLength localAlpha Neighbours 2) = 12 := by
  have hc := Atlas.GroupTheory.card_period_points (X := Neighbours) localAlpha 2
  rw [localAlpha_period_two_points_card] at hc
  omega

/-- The actual cyclic action has 432 four-cycles. -/
theorem localAlpha_four_cycles_card :
    Nat.card (Atlas.GroupTheory.CyclesOfLength localAlpha Neighbours 4) = 432 := by
  have hc := Atlas.GroupTheory.card_period_points (X := Neighbours) localAlpha 4
  rw [localAlpha_period_four_points_card] at hc
  omega

/-- The three fixed points are the three singleton orbits. -/
theorem localAlpha_one_cycles_card :
    Nat.card (Atlas.GroupTheory.CyclesOfLength localAlpha Neighbours 1) = 3 := by
  have hp : Nat.card {c : Neighbours // Function.minimalPeriod (localAlpha • ·) c = 1} = 3 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight localAlpha_period_one_iff)]
    exact localAlpha_fixed_card
  have hc := Atlas.GroupTheory.card_period_points (X := Neighbours) localAlpha 1
  rw [hp,mul_one] at hc
  exact hc.symm

end Atlas.Tits

