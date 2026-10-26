import Atlas.LinearGroups.F4.PairOrderReduction
import Atlas.LinearGroups.F4.PairScalarKernel
import Atlas.LinearGroups.F4.PairSpecialImageContainment

/-! Uniform order of the full intrinsic Albert stabilizer, through its actual
point stabilizer, opposite-pair quotient image and scalar kernel. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem card_oppositePairStabilizer :
    Nat.card (oppositePairStabilizer (F:=F))=(Nat.card F-1)*Nat.card F^9*
      (Nat.card F^2-1)*(Nat.card F^4-1)*(Nat.card F^6-1) := by
  rw [card_pair_eq_kernel_mul_image,pairOrthogonalHom_kernel_card,
    pairOrthogonalHom_range_eq_special]
  rw [show Nat.card (Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F))=
    Nat.card (Atlas.Orthogonal.SO_B 3 F) from rfl,card_specialB3]
  ring

theorem card_parabolic : Nat.card (parabolicPointStabilizer (F:=F))=
    Nat.card F^24*(Nat.card F-1)*(Nat.card F^2-1)*(Nat.card F^4-1)*(Nat.card F^6-1) := by
  rw [card_parabolic_eq_cell_mul_pair,card_oppositePairStabilizer]
  ring

/-- The same full polynomial-and-unit stabilizer used throughout the construction. -/
theorem card_Model : Nat.card (Model F)=
    Nat.card F^24*(Nat.card F^12-1)*(Nat.card F^8-1)*(Nat.card F^6-1)*(Nat.card F^2-1) := by
  let q := Nat.card F
  have hq : 1≤q := (Finite.one_lt_card (α:=F)).le
  have hs := geom_sum_mul_of_one_le hq 12
  have h4 : 1≤q^4 := one_le_pow₀ hq
  have hd : (q^4+1)*(q^4-1)=q^8-1 := by
    have h := Nat.sub_add_cancel h4
    have h8 : q^8=q^4*q^4 := by ring
    have h8pos : 1≤q^8 := one_le_pow₀ hq
    have h8sub := Nat.sub_add_cancel h8pos
    nlinarith
  rw [groupCard_eq_pointCount_mul_stabilizer,card_whiteZeroPoints_sum,card_parabolic]
  change (q^4+1)*(∑ i∈Finset.range 12,q^i)*(q^24*(q-1)*(q^2-1)*(q^4-1)*(q^6-1))=_
  calc
    _=q^24*((∑ i∈Finset.range 12,q^i)*(q-1))*((q^4+1)*(q^4-1))*(q^6-1)*(q^2-1) := by ring
    _=_ := by rw [hs,hd]

end Atlas.F4
