import Atlas.LinearGroups.F4.RadicalQuotientKernel
import Atlas.LinearGroups.F4.OrbitStabilizer
import Atlas.LinearGroups.Orthogonal.SpecialOrder

/-! Exact cardinal reductions for the actual opposite-pair quotient map.
The image and kernel remain explicit; the numerical F₄ formula is not assumed. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem card_pair_eq_kernel_mul_image :
    Nat.card (oppositePairStabilizer (F:=F))=
      Nat.card (pairOrthogonalHom (F:=F)).ker*Nat.card (pairOrthogonalHom (F:=F)).range := by
  have h := (pairOrthogonalHom (F:=F)).ker.card_mul_index
  rw [Subgroup.index_ker] at h
  exact h.symm

theorem card_model_eq_point_radical_kernel_image :
    Nat.card (Model F)=Nat.card (WhiteZeroPoints F)*Nat.card F^15*
      Nat.card (pairOrthogonalHom (F:=F)).ker*Nat.card (pairOrthogonalHom (F:=F)).range := by
  rw [groupCard_eq_pointCount_mul_stabilizer,card_parabolic_eq_cell_mul_pair,
    card_pair_eq_kernel_mul_image]
  ring

theorem card_specialB3 : Nat.card (Atlas.Orthogonal.SO_B 3 F)=
    Nat.card F^9*(Nat.card F^2-1)*(Nat.card F^4-1)*(Nat.card F^6-1) := by
  rw [Atlas.Orthogonal.card_specialB]
  norm_num [Finset.prod_range_succ]
  ring

end Atlas.F4
