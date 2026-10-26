import Atlas.LinearGroups.F4.SimpleCoroots

/-! Sparse symbolic Weyl-word identities, isolated from the root-selection helpers. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

attribute [local irreducible] simplePositive simpleNegative

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- Three-factor Weyl identity; multiplication by the unit-parameter Weyl
word has not yet been cancelled, keeping the symbolic expansion sparse. -/
theorem simpleWeyl_factorization (j : Fin 4) (a : Fˣ) :
    simplePositive j (a : F)*simpleNegative j ((a⁻¹ : Fˣ) : F)*simplePositive j (a : F)=
      diagonalTorus (simpleCorootParameters j a)*
        (simplePositive j 1*simpleNegative j 1*simplePositive j 1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (simplePositive j (a : F)).val ((simpleNegative j ((a⁻¹ : Fˣ) : F)).val
    ((simplePositive j (a : F)).val x)) =
      torusApply (simpleCorootParameters j a)
        ((simplePositive j 1).val ((simpleNegative j 1).val ((simplePositive j 1).val x)))
  simp only [simplePositive_apply,simpleNegative_apply]
  fin_cases j
  all_goals
    simp only [simplePositiveApply,simpleNegativeApply,torusLongApply,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',
      shortRootLinear_torusShortApply3,shortRootLinear_torusShortApply4]
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [Atlas.Albert.coordinateCycle,torusShortApply3,torusShortApply4,
          Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
          Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
          torusApply,Matrix.vecHead,Matrix.vecTail] <;>
          field_simp <;> ring
    · ext i k; fin_cases i <;> fin_cases k <;>
        simp [Atlas.Albert.coordinateCycle,torusShortApply3,torusShortApply4,
          Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
          Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
          torusApply,torusScale,weightCharacter,simpleCorootParameters,
          RootData.simpleCoefficients,RootData.coordinates,Weights.slotRoot,
          Fin.prod_univ_succ,Matrix.vecHead,Matrix.vecTail] <;>
          field_simp <;> ring


end Atlas.F4
