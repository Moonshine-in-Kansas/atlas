import Atlas.Algebra.IcosianNormOneKernelCard
import Atlas.Algebra.IcosianNormOneCard
import Atlas.Algebra.GoldenFourFinite
import Atlas.LinearGroups.ProjectiveSpecialLinear

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped MatrixGroups

theorem goldenFour_SL_card : Nat.card (Matrix.SpecialLinearGroup (Fin 2) GoldenFour)=60 := by
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  have hp := Atlas.card_psl_product (F := GoldenFour) 2
  rw [hc] at hp
  norm_num [Fin.prod_univ_two] at hp
  have hs := Atlas.card_psl_from_sl (ι := Fin 2) (F := GoldenFour)
  rw [hc] at hs
  norm_num at hs
  simpa only [Nat.card_eq_fintype_card] using hs.symm.trans hp

/-- Every determinant-one matrix lifts to an actual integral norm-one quaternion. -/
theorem icosianNormOneReduction_surjective : Function.Surjective icosianNormOneReduction := by
  have h := icosianNormOneReduction.ker.card_eq_card_quotient_mul_card_subgroup
  rw [icosianNormOneGroup_card,icosianNormOneReduction_kernel_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange icosianNormOneReduction).toEquiv] at h
  have hr : Nat.card icosianNormOneReduction.range=60 := by omega
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [hr,goldenFour_SL_card]

end Atlas.Algebra
