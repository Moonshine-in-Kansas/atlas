import Atlas.Algebra.Albert.RankOneChart
import Atlas.Algebra.SplitOctonion.PairNormCount
import Mathlib.FieldTheory.Finite.Basic

/-! An independent open-chart count on the trace-zero rank-one cone. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F]

def whiteZeroChartEquiv :
    (Σ a : Fˣ, {p : SplitOctonion.Carrier F × SplitOctonion.Carrier F //
      SplitOctonion.norm p.1 + SplitOctonion.norm p.2 = -(a.val)^2}) ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ trace x=0} where
  toFun p := ⟨rankOneChart p.1.val p.2.val.1 p.2.val.2,
    rankOneChart_adjoint _ p.1.ne_zero _ _,p.1.ne_zero,
    (rankOneChart_trace_zero_iff _ p.1.ne_zero _ _).mpr p.2.prop⟩
  invFun x := ⟨Units.mk0 (x.val.1 0) x.prop.2.1,
    (x.val.2 1,x.val.2 2),
    (rankOneChart_trace_zero_iff _ x.prop.2.1 _ _).mp (by
      rw [←eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1]
      exact x.prop.2.2)⟩
  left_inv p := by
    apply Sigma.ext
    · apply Units.ext; rfl
    · exact heq_of_eq (Subtype.ext rfl)
  right_inv x := Subtype.ext
    (eq_rankOneChart_of_adjoint_zero x.val x.prop.1 x.prop.2.1).symm

theorem card_whiteZero_first_diagonal [Finite F] :
    Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ trace x=0} =
      (Nat.card F - 1) * ((Nat.card F ^ 8 - 1) * Nat.card F ^ 7) := by
  classical
  letI := Fintype.ofFinite F
  rw [←Nat.card_congr (whiteZeroChartEquiv (F:=F)),Nat.card_sigma]
  have hc (a : Fˣ) : Nat.card {p : SplitOctonion.Carrier F × SplitOctonion.Carrier F //
      SplitOctonion.norm p.1 + SplitOctonion.norm p.2 = -(a.val)^2} =
      (Nat.card F ^ 8 - 1) * Nat.card F ^ 7 :=
    SplitOctonion.card_pairNorm_nonzero _ (neg_ne_zero.mpr (pow_ne_zero _ a.ne_zero))
  simp_rw [hc]
  simp [←Nat.card_eq_fintype_card,Nat.card_units]

end Atlas.Albert
