import Atlas.Algebra.IcosianNormOneReductionSurjective

noncomputable section
namespace Atlas.Algebra

theorem icosianNormOneReduction_kernel_iff (u : icosianNormOneGroup) :
    u∈icosianNormOneReduction.ker ↔ u=1 ∨ u=icosianNormOneMinusOne := by
  constructor
  · intro h
    rcases icosianNormOneReduction_kernel_values u h with h | h
    · exact Or.inl (icosianNormOne_value_injective h)
    · exact Or.inr (icosianNormOne_value_injective h)
  · rintro (rfl|rfl)
    · exact map_one _
    · exact icosianNormOneReduction_minus_one

/-- The actual norm-one scalar group modulo its two signs. -/
abbrev IcosianScalarProjectiveModel := icosianNormOneGroup ⧸ icosianNormOneReduction.ker

/-- Reduction identifies the actual scalar sign quotient with SL2(F4). -/
def icosianScalarProjectiveSL :
    IcosianScalarProjectiveModel ≃* Matrix.SpecialLinearGroup (Fin 2) GoldenFour :=
  QuotientGroup.quotientKerEquivOfSurjective _ icosianNormOneReduction_surjective

theorem icosianScalarProjective_card : Nat.card IcosianScalarProjectiveModel=60 := by
  rw [Nat.card_congr icosianScalarProjectiveSL.toEquiv,goldenFour_SL_card]

end Atlas.Algebra
