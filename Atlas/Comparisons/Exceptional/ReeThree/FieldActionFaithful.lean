import Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget

/-! Faithfulness of the coefficient-field action on the independent semilinear
target. These results do not identify that target with the small Ree source. -/

noncomputable section
namespace Atlas.Comparisons.ReeThree
open scoped MatrixGroups
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem linearFactor_center_trivial (hF : Nat.card F = 2)
    (hdeg : Module.finrank F K = 3) : Subgroup.center SL(2,K) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Atlas.card_sl_center (ι := Fin 2) (F := K), scalar_card F K hF hdeg]
  norm_num

theorem fieldAction_injective (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    Function.Injective (fieldAction F K) := by
  have hq : Function.Injective (QuotientGroup.mk' (Subgroup.center SL(2,K))) := by
    apply (QuotientGroup.mk' (Subgroup.center SL(2,K))).ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk',linearFactor_center_trivial F K hF hdeg]
  intro s t he
  apply AlgEquiv.ext
  intro x
  let u : SL(2,K) := Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
    (j := 1) (by decide) x
  have hu := congrArg (fun f : MulAut PSL(2,K) => f (QuotientGroup.mk' _ u)) he
  change QuotientGroup.mk' _ (Atlas.fieldEquivSL 2 s.toRingEquiv u) =
    QuotientGroup.mk' _ (Atlas.fieldEquivSL 2 t.toRingEquiv u) at hu
  have hc := congrArg (fun g : SL(2,K) => g.val 0 1) (hq hu)
  simpa [Atlas.fieldEquivSL,u,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe] using hc

/-- The Frobenius action really has order three on the projective group. -/
theorem projectiveFrobenius_order (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    orderOf (fieldAction F K (Atlas.FiniteCubic.sigma F K)) = 3 := by
  rw [orderOf_injective (fieldAction F K) (fieldAction_injective F K hF hdeg)]
  exact frobenius_order F K hdeg

end Atlas.Comparisons.ReeThree
