import Atlas.LinearGroups.ReeF4.ChartPositiveConjugates
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem chartLongConjugate_formula_0 (m : ℕ) (a : F) (w : Carrier F) :
    carrierConjugate (chartLongPermutation 0) (longSL2Formula a (theta F m a)) w =
      alternatingLongFormula m 3 a w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [carrierConjugate,chartLongPermutation,chartLongPermutation,
      carrierPermute,weylSigmaPermutation,weylRhoPermutation,weylRhoIndex,weylSigmaIndex,
      Equiv.Perm.one_def,Equiv.Perm.mul_def,pow_succ,wilsonCoordinatesEquiv,shortRootParameterFormula,shortRootCenterFormula,
      longSL2Formula,ree_f4_factor_rows] <;> ring_nf <;> try simp [CharTwo.ofNat_eq_mod]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [carrierConjugate,chartLongPermutation,chartLongPermutation,
      carrierPermute,weylSigmaPermutation,weylRhoPermutation,weylRhoIndex,weylSigmaIndex,
      Equiv.Perm.one_def,Equiv.Perm.mul_def,pow_succ,wilsonCoordinatesEquiv,shortRootParameterFormula,shortRootCenterFormula,
      longSL2Formula,ree_f4_factor_rows] <;> ring_nf <;> try simp [CharTwo.ofNat_eq_mod]

theorem chartLongConjugate_eq_positive_0 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) :
    chartLongConjugate hcard 0 a=positiveLongFactor hcard 3 a := by
  apply model_ext_of_carrier_action
  intro w
  rw [chartLongConjugate_val]
  simpa only [positiveLongFactor,alternatingShortFactor_pair_val,alternatingLongFactor_val] using
    chartLongConjugate_formula_0 m a w.val
end Atlas.ReeF4
