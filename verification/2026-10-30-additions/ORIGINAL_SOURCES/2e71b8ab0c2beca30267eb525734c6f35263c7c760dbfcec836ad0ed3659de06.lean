import Atlas.LinearGroups.ReeF4.ChartPositiveConjugates
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem chartShortConjugate_formula_1 (m : ℕ) (a b : F) (w : Carrier F) :
    carrierConjugate (chartShortPermutation 1) (shortRootParameterFormula (theta F m).toRingHom a ∘ shortRootCenterFormula (theta F m).toRingHom b) w =
      alternatingShortFormula m 2 a b w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [carrierConjugate,chartShortPermutation,chartLongPermutation,
      carrierPermute,weylSigmaPermutation,weylRhoPermutation,weylRhoIndex,weylSigmaIndex,
      Equiv.Perm.one_def,Equiv.Perm.mul_def,pow_succ,wilsonCoordinatesEquiv,shortRootParameterFormula,shortRootCenterFormula,
      longSL2Formula,ree_f4_factor_rows] <;> ring_nf <;> try simp [CharTwo.ofNat_eq_mod]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [carrierConjugate,chartShortPermutation,chartLongPermutation,
      carrierPermute,weylSigmaPermutation,weylRhoPermutation,weylRhoIndex,weylSigmaIndex,
      Equiv.Perm.one_def,Equiv.Perm.mul_def,pow_succ,wilsonCoordinatesEquiv,shortRootParameterFormula,shortRootCenterFormula,
      longSL2Formula,ree_f4_factor_rows] <;> ring_nf <;> try simp [CharTwo.ofNat_eq_mod]

theorem chartShortConjugate_eq_positive_1 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a b : F) :
    chartShortConjugate hcard 1 a b=positiveShortFactor hcard 2 a b := by
  apply model_ext_of_carrier_action
  intro w
  rw [chartShortConjugate_val]
  simpa only [positiveShortFactor,alternatingShortFactor_pair_val,alternatingLongFactor_val] using
    chartShortConjugate_formula_1 m a b w.val
end Atlas.ReeF4
