import Atlas.LinearGroups.Triality.RankOneGenerators
import Atlas.LinearGroups.Elementary

/-! The central-node SL₂ over the base field, inside the literal matrix group. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Matrix
variable {K : Type*} [Field K]

def coordinateCycleLinear : VectorD 4 K ≃ₗ[K] VectorD 4 K where
  toFun x := Sum.elim ![x (.inl 2),x (.inl 0),x (.inl 1),x (.inl 3)]
    ![x (.inr 2),x (.inr 0),x (.inr 1),x (.inr 3)]
  invFun x := Sum.elim ![x (.inl 1),x (.inl 2),x (.inl 0),x (.inl 3)]
    ![x (.inr 1),x (.inr 2),x (.inr 0),x (.inr 3)]
  left_inv x := by ext i; rcases i with i|i <;> fin_cases i <;> rfl
  right_inv x := by ext i; rcases i with i|i <;> fin_cases i <;> rfl
  map_add' x y := by ext i; rcases i with i|i <;> fin_cases i <;> rfl
  map_smul' c x := by ext i; rcases i with i|i <;> fin_cases i <;> rfl

def coordinateCycle : O_DPlus 4 K := ⟨coordinateCycleLinear, by
  intro x
  simp [formD_apply, coordinateCycleLinear, Fin.sum_univ_succ]
  ring⟩

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def rankOneLongOrthogonal : SpecialLinearGroup (Fin 2) F →* O_DPlus 4 K :=
  (MulAut.conj coordinateCycle).toMonoidHom.comp
    (blockEmbedding.comp
      (((D2Matrix.toOrthogonal).comp
        ((1 : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) K).prod
          (contragredient.comp (SpecialLinearGroup.map (algebraMap F K))))).prod 1))

set_option maxHeartbeats 3000000 in
theorem rankOneLongOrthogonal_upper (a : F) :
    rankOneLongOrthogonal F K (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      longRoot F K a := by
  change coordinateCycle * blockEmbedding (D2Matrix.toOrthogonal
    (1,contragredient (SpecialLinearGroup.map (algebraMap F K)
      (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a))),1) * coordinateCycle⁻¹ = _
  rw [map_transvection,contragredient_transvection]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [coordinateCycle, coordinateCycleLinear, blockEmbedding, blockLinear, splitBlocks,
      D2Matrix.toOrthogonal, D2Matrix.onD, D2Matrix.coordinates, D2Matrix.matrixAction,
      SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
      Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      longRoot, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply,
      Subgroup.coe_mul, LinearEquiv.mul_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 3000000 in
theorem rankOneLongOrthogonal_lower (a : F) :
    rankOneLongOrthogonal F K (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      longNegativeRoot F K a := by
  change coordinateCycle * blockEmbedding (D2Matrix.toOrthogonal
    (1,contragredient (SpecialLinearGroup.map (algebraMap F K)
      (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a))),1) * coordinateCycle⁻¹ = _
  rw [map_transvection,contragredient_transvection]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [coordinateCycle, coordinateCycleLinear, blockEmbedding, blockLinear, splitBlocks,
      D2Matrix.toOrthogonal, D2Matrix.onD, D2Matrix.coordinates, D2Matrix.matrixAction,
      SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
      Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      longNegativeRoot, pinnedRoot, pinnedNegativeRoot, differenceRoot_apply,
      Subgroup.coe_mul, LinearEquiv.mul_apply, e, f, Algebra.smul_def] <;> ring

theorem rankOneLongOrthogonal_mem (g : SpecialLinearGroup (Fin 2) F) :
    rankOneLongOrthogonal F K g ∈ generated F K := by
  apply Atlas.sl_elementary_induction
    (fun g => rankOneLongOrthogonal F K g ∈ generated F K) _ _ g
  · intro i j hij a
    fin_cases i <;> fin_cases j <;> try contradiction
    · rw [rankOneLongOrthogonal_upper]
      exact longRoot_mem F K a
    · rw [rankOneLongOrthogonal_lower]
      exact longNegativeRoot_mem F K a
  · intro g h hg hh
    rw [map_mul]
    exact Subgroup.mul_mem _ hg hh

def rankOneLong : SpecialLinearGroup (Fin 2) F →* Group F K :=
  (rankOneLongOrthogonal F K).codRestrict (generated F K) (rankOneLongOrthogonal_mem F K)

end Atlas.Triality
