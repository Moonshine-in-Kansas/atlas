import Atlas.Algebra.Albert.RankOneChart
import Atlas.Algebra.SplitOctonion.NormCounts
import Mathlib.FieldTheory.Finite.Basic

/-! Direct diagonal-boundary counts within the first rank-one chart. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F]

theorem rankOneChart_third_zero_iff (a : F) (ha : a≠0)
    (B C : SplitOctonion.Carrier F) :
    (rankOneChart a B C).1 2=0 ↔ SplitOctonion.norm B=0 := by
  change a⁻¹ * SplitOctonion.norm B=0 ↔ _
  simp [ha]

def chartThirdZeroEquiv :
    (Fˣ × {B : SplitOctonion.Carrier F // SplitOctonion.norm B=0} ×
      SplitOctonion.Carrier F) ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 2=0} where
  toFun p := ⟨rankOneChart p.1.val p.2.1.val p.2.2,
    rankOneChart_adjoint _ p.1.ne_zero _ _,p.1.ne_zero,
    (rankOneChart_third_zero_iff _ p.1.ne_zero _ _).mpr p.2.1.prop⟩
  invFun x := (Units.mk0 (x.val.1 0) x.prop.2.1,
    ⟨x.val.2 1,(rankOneChart_third_zero_iff _ x.prop.2.1 _ _).mp (by
      rw [←eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1]
      exact x.prop.2.2)⟩,x.val.2 2)
  left_inv p := by
    apply Prod.ext
    · apply Units.ext; rfl
    · rfl
  right_inv x := Subtype.ext
    (eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1).symm

theorem card_chart_third_zero [Finite F] :
    Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 2=0} =
      (Nat.card F-1) *
      ((Nat.card F^4+(Nat.card F^4-1)*Nat.card F^3) * Nat.card F^8) := by
  rw [←Nat.card_congr (chartThirdZeroEquiv (F:=F)),Nat.card_prod,Nat.card_prod,
    Nat.card_units,SplitOctonion.card_norm_zero]
  simp [SplitOctonion.Carrier,Nat.card_fun]

def whiteChartThirdZeroEquiv :
    (Σ a : Fˣ, {B : SplitOctonion.Carrier F // SplitOctonion.norm B=0} ×
      {C : SplitOctonion.Carrier F // SplitOctonion.norm C= -(a.val)^2}) ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 2=0 ∧ trace x=0} where
  toFun p := ⟨rankOneChart p.1.val p.2.1.val p.2.2.val,
    rankOneChart_adjoint _ p.1.ne_zero _ _,p.1.ne_zero,
    (rankOneChart_third_zero_iff _ p.1.ne_zero _ _).mpr p.2.1.prop,
    (rankOneChart_trace_zero_iff _ p.1.ne_zero _ _).mpr (by
      rw [p.2.1.prop,zero_add,p.2.2.prop])⟩
  invFun x := ⟨Units.mk0 (x.val.1 0) x.prop.2.1,
    (chartThirdZeroEquiv.symm ⟨x.val,x.prop.1,x.prop.2.1,x.prop.2.2.1⟩).2.1,
    ⟨x.val.2 2,by
      have hn := (chartThirdZeroEquiv.symm
        ⟨x.val,x.prop.1,x.prop.2.1,x.prop.2.2.1⟩).2.1.prop
      have ht := (rankOneChart_trace_zero_iff _ x.prop.2.1 (x.val.2 1) (x.val.2 2)).mp (by
        rw [←eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1]
        exact x.prop.2.2.2)
      change SplitOctonion.norm (x.val.2 1)=0 at hn
      simpa only [hn,zero_add,Units.val_mk0] using ht⟩⟩
  left_inv p := by
    apply Sigma.ext
    · apply Units.ext; rfl
    · apply heq_of_eq; rfl
  right_inv x := Subtype.ext
    (eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1).symm

theorem card_white_chart_third_zero [Finite F] :
    Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 2=0 ∧ trace x=0} =
      (Nat.card F-1) *
      ((Nat.card F^4+(Nat.card F^4-1)*Nat.card F^3) *
        ((Nat.card F^4-1)*Nat.card F^3)) := by
  classical
  letI := Fintype.ofFinite F
  rw [←Nat.card_congr (whiteChartThirdZeroEquiv (F:=F)),Nat.card_sigma]
  simp_rw [Nat.card_prod,SplitOctonion.card_norm_zero]
  have hc (a : Fˣ) : Nat.card {C : SplitOctonion.Carrier F //
      SplitOctonion.norm C= -(a.val)^2} = (Nat.card F^4-1)*Nat.card F^3 :=
    SplitOctonion.card_norm_nonzero _ (neg_ne_zero.mpr (pow_ne_zero _ a.ne_zero))
  simp_rw [hc]
  simp [←Nat.card_eq_fintype_card,Nat.card_units]

theorem rankOneChart_second_zero_iff (a : F) (ha : a≠0)
    (B C : SplitOctonion.Carrier F) :
    (rankOneChart a B C).1 1=0 ↔ SplitOctonion.norm C=0 := by
  change a⁻¹ * SplitOctonion.norm C=0 ↔ _
  simp [ha]

def chartTwoZeroEquiv :
    (Fˣ × {B : SplitOctonion.Carrier F // SplitOctonion.norm B=0} ×
      {C : SplitOctonion.Carrier F // SplitOctonion.norm C=0}) ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 1=0 ∧ x.1 2=0} where
  toFun p := ⟨rankOneChart p.1.val p.2.1.val p.2.2.val,
    rankOneChart_adjoint _ p.1.ne_zero _ _,p.1.ne_zero,
    (rankOneChart_second_zero_iff _ p.1.ne_zero _ _).mpr p.2.2.prop,
    (rankOneChart_third_zero_iff _ p.1.ne_zero _ _).mpr p.2.1.prop⟩
  invFun x := (Units.mk0 (x.val.1 0) x.prop.2.1,
    ⟨x.val.2 1,(rankOneChart_third_zero_iff _ x.prop.2.1 _ _).mp (by
      rw [←eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1]
      exact x.prop.2.2.2)⟩,
    ⟨x.val.2 2,(rankOneChart_second_zero_iff _ x.prop.2.1 _ _).mp (by
      rw [←eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1]
      exact x.prop.2.2.1)⟩)
  left_inv p := by
    apply Prod.ext
    · apply Units.ext; rfl
    · rfl
  right_inv x := Subtype.ext
    (eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1).symm

theorem card_chart_two_zero [Finite F] :
    Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 1=0 ∧ x.1 2=0} =
      (Nat.card F-1) * (Nat.card F^4+(Nat.card F^4-1)*Nat.card F^3)^2 := by
  rw [←Nat.card_congr (chartTwoZeroEquiv (F:=F)),Nat.card_prod,Nat.card_prod,
    Nat.card_units,SplitOctonion.card_norm_zero,pow_two]

end Atlas.Albert
