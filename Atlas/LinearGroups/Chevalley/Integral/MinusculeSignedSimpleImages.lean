import Atlas.LinearGroups.Chevalley.Integral.MinusculeCartanOperators
/-! Explicit polynomial conjugation on the signed
simple-root image block; no factorial division or global J assumption. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} (S : Strings I Ω) (R : Type*) [CommRing R]

theorem raising_lowering_raising (i : I) :
    S.raising R i * S.lowering R i * S.raising R i = S.raising R i := by
  apply Finsupp.lhom_ext
  intro μ r
  simp only [Module.End.mul_apply]
  rcases S.minuscule i μ with h | h | h
  all_goals simp [raising, lowering, step_single, h, S.pairing_reflection, S.involutive i μ]

theorem lowering_raising_lowering (i : I) :
    S.lowering R i * S.raising R i * S.lowering R i = S.lowering R i := by
  apply Finsupp.lhom_ext
  intro μ r
  simp only [Module.End.mul_apply]
  rcases S.minuscule i μ with h | h | h
  all_goals simp [raising, lowering, step_single, h, S.pairing_reflection, S.involutive i μ]

/-- The t-squared coefficient is integral even in characteristic two. -/
theorem raising_conjugate_lowering (i : I) (t : R) :
    S.transvection R i (-1) t * S.lowering R i * S.transvection R i (-1) (-t) =
      S.lowering R i + t • S.gradeOperator R i - (t^2) • S.raising R i := by
  rw [← S.raising_lowering_sub R i]
  simp only [transvection, raising, lowering, mul_add, add_mul,
    one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hefe := S.raising_lowering_raising R i
  change S.step R i (-1) * S.step R i 1 * S.step R i (-1) = S.step R i (-1) at hefe
  rw [hefe]
  module

/-- Compatible signed images: v_-i -> sigma F_i, u_i -> sigma H_i,
v_i -> -sigma E_i. This is the literal quadratic Geck special column. -/
theorem raising_conjugate_signed_lowering (i : I) (t σ : R) :
    S.transvection R i (-1) t * (σ • S.lowering R i) * S.transvection R i (-1) (-t) =
      σ • S.lowering R i + t • (σ • S.gradeOperator R i) +
        (t^2) • ((-σ) • S.raising R i) := by
  rw [mul_smul_comm, smul_mul_assoc, S.raising_conjugate_lowering]
  module
end Atlas.Chevalley.Integral.Minuscule.Strings
