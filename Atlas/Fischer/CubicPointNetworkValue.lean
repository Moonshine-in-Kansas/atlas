import Atlas.Fischer.CubicPointVectorFamilies

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact pure-point six-index network, obtained through two applications of
the structural vector formula and the symbolic contractions over one or two indices. -/
theorem cubicPointNetwork_value (p q r : Omega) :
    cubicPointNetwork (cubicPointPattern p) (cubicPointPattern q) (cubicPointPattern r)=
      511705088*cubicPointPattern p q r+475791360 := by
  have hr (s : Omega) : cubicPointMatrixRowSum (cubicPointPattern s)=cubicPointRowSum s := by
    funext i
    exact cubicPointPattern_row_sum s i
  rw [cubicPointNetwork_reduction,hr,hr,hr]
  have hpr (a : Omega) :
      cubicPointVector (cubicPointPattern p a) (cubicPointRowSum q) (cubicPointPattern r a)=
      cubicPointVector (cubicPointPattern p a) (cubicPointPattern r a) (cubicPointRowSum q) :=
    cubicPointVector_swap_last _ _ _
  have hqr (a : Omega) :
      cubicPointVector (cubicPointRowSum p) (cubicPointPattern q a) (cubicPointPattern r a)=
      cubicPointVector (cubicPointPattern q a) (cubicPointPattern r a) (cubicPointRowSum p) := by
    rw [cubicPointVector_swap_first,cubicPointVector_swap_last]
  simp_rw [hpr,hqr]
  rw [cubicPointPattern_vector_rows,cubicPointVector_two_rows_sum,
    cubicPointVector_two_rows_sum,cubicPointVector_two_rows_sum,cubicPointVector_three_rows_sum]
  simp_rw [cubicPointPattern_hadamard_weighted,cubicPointPattern_pair_sum,
    cubicPointPattern_row_pair,cubicPointPattern_hadamard_triple,
    cubicPointRowSum_pair_sum,cubicPointRowSum_triple_sum]
  by_cases hpq : p=q
  · subst q
    by_cases hpr : p=r
    · subst r
      simp [cubicPointPattern,cubicPointRowSum,cubicPointDeltaSum,cubicPointDeltaAll]
      norm_num
    · simp [cubicPointPattern,cubicPointRowSum,cubicPointDeltaSum,cubicPointDeltaAll,hpr,Ne.symm hpr]
      norm_num
  · by_cases hpr : p=r
    · subst r
      simp [cubicPointPattern,cubicPointRowSum,cubicPointDeltaSum,cubicPointDeltaAll,hpq,Ne.symm hpq]
      norm_num
    · by_cases hqr : q=r
      · subst r
        simp [cubicPointPattern,cubicPointRowSum,cubicPointDeltaSum,cubicPointDeltaAll,hpq,Ne.symm hpq]
        norm_num
      · simp [cubicPointPattern,cubicPointRowSum,cubicPointDeltaSum,cubicPointDeltaAll,
          hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr]
        norm_num

end Atlas.Fischer
