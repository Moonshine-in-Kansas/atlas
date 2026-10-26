import Atlas.LinearGroups.Triality.RankOneMaps

noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Matrix
variable {K : Type*} [Field K]

theorem signTwist_transvection (i j : Fin 2) (hij : i ≠ j) (a : K) :
    signTwist (SpecialLinearGroup.transvection hij a) = SpecialLinearGroup.transvection hij (-a) := by
  apply Subtype.ext
  change signMatrix (Matrix.transvection i j a) = Matrix.transvection i j (-a)
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals ext k l; fin_cases k <;> fin_cases l <;> simp [signMatrix, Matrix.transvection]

theorem contragredient_transvection (i j : Fin 2) (hij : i ≠ j) (a : K) :
    contragredient (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection (Ne.symm hij) (-a) := by
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij a)⁻¹.val.transpose = _
  rw [SpecialLinearGroup.transvection_inv]
  ext k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.transvection]

theorem map_transvection {L : Type*} [Field L] (e : K →+* L)
    (i j : Fin 2) (hij : i ≠ j) (a : K) :
    SpecialLinearGroup.map e (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij (e a) := by
  ext k l
  fin_cases k <;> fin_cases l <;> fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.transvection_coe, Matrix.transvection]

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankOneShortOrthogonal_apply (g : SpecialLinearGroup (Fin 2) K) :
    rankOneShortOrthogonal F K g = blockEmbedding
      (D2Matrix.toOrthogonal (1,contragredient g), D2Matrix.toOrthogonal
        (signTwist (SpecialLinearGroup.map
          ((FiniteCubic.sigma F K).toRingHom.comp (FiniteCubic.sigma F K).toRingHom) g),
        contragredient (SpecialLinearGroup.map (FiniteCubic.sigma F K).toRingHom g))) := rfl

set_option maxHeartbeats 3000000 in
theorem rankOneShortOrthogonal_upper (a : K) :
    rankOneShortOrthogonal F K (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      shortRoot F K a := by
  rw [rankOneShortOrthogonal_apply, map_transvection, map_transvection,
    signTwist_transvection, contragredient_transvection, contragredient_transvection]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [blockEmbedding, blockLinear, splitBlocks,
      D2Matrix.toOrthogonal, D2Matrix.onD, D2Matrix.coordinates, D2Matrix.matrixAction,
      SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
      Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      shortRoot, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply, sumRoot_apply,
      negativeSumRoot_apply, Subgroup.coe_mul, LinearEquiv.mul_apply, e, f] <;> ring

set_option maxHeartbeats 3000000 in
theorem rankOneShortOrthogonal_lower (a : K) :
    rankOneShortOrthogonal F K (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      shortNegativeRoot F K a := by
  rw [rankOneShortOrthogonal_apply, map_transvection, map_transvection,
    signTwist_transvection, contragredient_transvection, contragredient_transvection]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [blockEmbedding, blockLinear, splitBlocks,
      D2Matrix.toOrthogonal, D2Matrix.onD, D2Matrix.coordinates, D2Matrix.matrixAction,
      SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
      Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      shortNegativeRoot, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply, sumRoot_apply,
      negativeSumRoot_apply, Subgroup.coe_mul, LinearEquiv.mul_apply, e, f] <;> ring

end Atlas.Triality
