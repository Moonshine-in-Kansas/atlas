import Atlas.Fischer.DuadWordOctadLabels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The complete407-term expression has its exact nonzero coefficient at each
actual word label; no two shortened words contribute to the same coordinate. -/
theorem duadSignedCoordinateExpression_at_word (p : Finset Omega) (hp : p.Nonempty)
    (η : DuadCoordinateWord p → Bit) (ξ : Module.Dual Bit (duadShortenedCode p))
    (c : DuadCoordinateWord p) :
    duadSignedCoordinateExpression p η ξ (.inr (duadWordOctad p c))=
      (1/8 : Scalar) * parkerScalarSign (η c + ξ c.val) * duadWordScalar p c := by
  classical
  have hz : duadicAxisPart p (.inr (duadWordOctad p c))=0 := by
    simp [duadicAxisPart,axisSum]
  have hi (d : DuadCoordinateWord p) : duadWordOctad p c=duadWordOctad p d ↔ c=d :=
    (duadWordOctad_injective p hp).eq_iff
  simp only [duadSignedCoordinateExpression,Pi.smul_apply,smul_eq_mul,Pi.add_apply,hz,
    zero_add,Finset.sum_apply,duadWordVector_octad,xOctad_octad_apply,hi,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

theorem duadSignedCoordinateExpression_at_word_ne_zero (p : Finset Omega) (hp : p.Nonempty)
    (η : DuadCoordinateWord p → Bit) (ξ : Module.Dual Bit (duadShortenedCode p))
    (c : DuadCoordinateWord p) :
    duadSignedCoordinateExpression p η ξ (.inr (duadWordOctad p c)) ≠ 0 := by
  rw [duadSignedCoordinateExpression_at_word p hp]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (parkerScalarSign_ne_zero _))
    (duadWordScalar_ne_zero p c)

/-- Weight eight contributes real coefficients, weight sixteen imaginary ones. -/
theorem duadSignedCoordinateExpression_at_word_star (p : Finset Omega) (hp : p.Nonempty)
    (η : DuadCoordinateWord p → Bit) (ξ : Module.Dual Bit (duadShortenedCode p))
    (c : DuadCoordinateWord p) :
    star (duadSignedCoordinateExpression p η ξ (.inr (duadWordOctad p c))) =
      if hammingNorm c.val.val.val=8 then
        duadSignedCoordinateExpression p η ξ (.inr (duadWordOctad p c)) else
        -duadSignedCoordinateExpression p η ξ (.inr (duadWordOctad p c)) := by
  rw [duadSignedCoordinateExpression_at_word p hp]
  simp only [duadWordScalar]
  split_ifs <;> simp [map_mul,parkerScalarSign_star,theta_conjugate] <;> ring

end Atlas.Fischer
