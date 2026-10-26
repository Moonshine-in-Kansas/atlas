import Atlas.Tits.TransferRowOrbitFibres
import Atlas.Tits.TransferGeometricProduct

/-! Cancellation of the genuine global two-cycle factors, grouped by their
six coordinate rows. -/

namespace Atlas.Tits
open Atlas.Rudvalis
open scoped BigOperators Classical

abbrev AlphaTwoCycles := {O : AlphaCycles // Nat.card O.orbit = 2}
abbrev ExternalRows := {p : Point // p ≠ rowLabel 0}

noncomputable def alphaTwoCycleRow (O : AlphaTwoCycles) : ExternalRows :=
  (alpha_two_cycle_unique_row O.val O.prop).exists.choose

theorem alphaTwoCycleRow_spec (O : AlphaTwoCycles) :
    AlphaCycleInRow (alphaTwoCycleRow O).val O.val :=
  (alpha_two_cycle_unique_row O.val O.prop).exists.choose_spec

noncomputable def alphaTwoCyclesEquivRows :
    AlphaTwoCycles ≃ Σ p : ExternalRows, {O : AlphaCycles // AlphaCycleInRow p.val O} where
  toFun O := ⟨alphaTwoCycleRow O,⟨O.val,alphaTwoCycleRow_spec O⟩⟩
  invFun R := ⟨R.2.val,alphaCycle_row_card R.1.val R.1.prop R.2.val R.2.prop⟩
  left_inv O := Subtype.ext rfl
  right_inv R := by
    rcases R with ⟨p,O⟩
    have he : alphaTwoCycleRow
        ⟨O.val,alphaCycle_row_card p.val p.prop O.val O.prop⟩ = p :=
      (alpha_two_cycle_unique_row O.val
        (alphaCycle_row_card p.val p.prop O.val O.prop)).unique
        (alphaTwoCycleRow_spec _) O.prop
    apply Sigma.ext he
    apply (Subtype.heq_iff_coe_eq (by intro Q; dsimp only; rw [he])).mpr
    rfl

theorem alphaCycleValue_row_constant (p : ExternalRows) (O P : AlphaCycles)
    (hO : AlphaCycleInRow p.val O) (hP : AlphaCycleInRow p.val P) :
    geometricCycleValue localAlpha O = geometricCycleValue localAlpha P := by
  have ho := alphaCycle_row_card p.val p.prop O hO
  have hp := alphaCycle_row_card p.val p.prop P hP
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq',
    Atlas.GroupTheory.card_zpowers_orbit_eq_minimalPeriod] at ho
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out P Quotient.out_eq',
    Atlas.GroupTheory.card_zpowers_orbit_eq_minimalPeriod] at hp
  rw [geometricCycleValue_out,geometricCycleValue_out]
  unfold pointCycleValue
  simp only [ho,hp]
  exact multiplierAt_alpha_square_row_constant p.val p.prop O.out P.out hO hP _ _

theorem alphaCycleValue_two_square (O : AlphaTwoCycles) :
    (geometricCycleValue localAlpha O.val)^2 = 1 := by
  have ho := O.prop
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O.val Quotient.out_eq',
    Atlas.GroupTheory.card_zpowers_orbit_eq_minimalPeriod] at ho
  rw [geometricCycleValue_out]
  unfold pointCycleValue
  simp only [ho]
  exact multiplierAt_alpha_square_square O.val.out _

theorem alpha_row_cycle_product (p : ExternalRows) :
    ∏ O : {O : AlphaCycles // AlphaCycleInRow p.val O},
      geometricCycleValue localAlpha O.val = 1 := by
  classical
  letI := Fintype.ofFinite {O : AlphaCycles // AlphaCycleInRow p.val O}
  have hc := alpha_global_cycles_in_row_card p.val p.prop
  have hn : Nonempty {O : AlphaCycles // AlphaCycleInRow p.val O} :=
    (Nat.card_pos_iff.mp (by omega)).1
  let O := Classical.choice hn
  have he (P : {O : AlphaCycles // AlphaCycleInRow p.val O}) :
      geometricCycleValue localAlpha P.val = geometricCycleValue localAlpha O.val :=
    alphaCycleValue_row_constant p P.val O.val P.prop O.prop
  simp only [he,Finset.prod_const,Finset.card_univ,←Nat.card_eq_fintype_card,hc]
  exact alphaCycleValue_two_square
    ⟨O.val,alphaCycle_row_card p.val p.prop O.val O.prop⟩

/-- All twelve actual two-cycle factors cancel, two in each external row. -/
theorem alpha_two_cycle_product :
    ∏ O : AlphaTwoCycles, geometricCycleValue localAlpha O.val = 1 := by
  classical
  rw [Fintype.prod_equiv alphaTwoCyclesEquivRows
    (fun O => geometricCycleValue localAlpha O.val)
    (fun R => geometricCycleValue localAlpha R.2.val) (fun _ => rfl)]
  rw [Fintype.prod_sigma]
  apply Finset.prod_eq_one
  intro p hp
  exact alpha_row_cycle_product p

end Atlas.Tits
