import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2Index
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2IntegerTemplate
/-! Exact integral C2 Geck raising operators in the certified ten-dimensional basis. -/
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData C2IntegerTemplate
open scoped Matrix

theorem functional_eq_coordinates (v w : Fin 2 → ℤ) :
    functional v = functional w ↔ v = w := by
  constructor
  · intro h
    simpa using congrArg (functionalCoordinates 2) h
  · exact congrArg functional

theorem functional_add_coordinates (v w : Fin 2 → ℤ) :
    functional v + functional w = functional (v+w) := by
  ext x
  simp [functional_apply, dot_add_left]

theorem c_chain_bot_zero (j : Fin 8) :
    (pairingC 2).chainBotCoeff (label 0) (label j) = cBot 0 j :=
  c_chain_bot 0 j

theorem c_chain_bot_one (j : Fin 8) :
    (pairingC 2).chainBotCoeff (label 1) (label j) = cBot 1 j :=
  c_chain_bot 1 j

theorem labelEquiv_apply (i : Fin 8) : labelEquiv i = label i := rfl

theorem c_reflection_self_label (i : Fin 8) :
    (pairingC 2).reflectionPerm (label i) (label i) = label (oppositeLabel i) := by
  simpa only [RootPairing.indexNeg_neg] using c_neg_label i

/-- Explicit finite inverse coordinate split; no root data is assumed here. -/
theorem c2_sum_split (i : Fin 10) :
    (finSumFinEquiv : Fin 2 ⊕ Fin 8 ≃ Fin 10).symm i =
      ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2,
        Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7] i := by
  fin_cases i <;> rfl

/-- Exact integral operators, before any coefficient reduction. -/
theorem c2ActualRaising_zero : c2ActualRaising 0 = (ea : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [c2ActualRaising, c2IndexEquiv, c2_sum_split, labelEquiv_apply,
      label_injective.eq_iff,
      RootPairing.GeckConstruction.e, c_simple_label, c_neg_label, c_reflection_self_label,
      c_chain_bot_zero, c_chain_bot_one, cBot, baseC_cartan, CartanMatrix.C, CartanMatrix.B, c_root_label, functional_add_coordinates,
      functional_eq_coordinates, funext_iff, Fin.forall_fin_succ, cCoordinates, oppositeLabel,
      simpleLabelIndex, ea, Matrix.fromBlocks, functional_apply, dot,
      Fin.sum_univ_succ] <;> decide

theorem c2ActualRaising_one : c2ActualRaising 1 = (eb : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [c2ActualRaising, c2IndexEquiv, c2_sum_split, labelEquiv_apply,
      label_injective.eq_iff,
      RootPairing.GeckConstruction.e, c_simple_label, c_neg_label, c_reflection_self_label,
      c_chain_bot_zero, c_chain_bot_one, cBot, baseC_cartan, CartanMatrix.C, CartanMatrix.B, c_root_label, functional_add_coordinates,
      functional_eq_coordinates, funext_iff, Fin.forall_fin_succ, cCoordinates, oppositeLabel,
      simpleLabelIndex, eb, Matrix.fromBlocks, functional_apply, dot,
      Fin.sum_univ_succ] <;> decide

end Atlas.Chevalley.Integral.RankTwo
