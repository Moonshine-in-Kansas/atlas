import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation

/-! Same-root Weyl exchange on the original minuscule basis. Only the three
possible grades are used; no negation-closed weight set is assumed. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} (S : Strings I Ω) (R : Type*) [CommRing R]

theorem weylEquiv_one_mul_lowering (i : I) (t : R) :
    S.weylEquiv R i 1 * S.rootEquiv R i 1 (by decide) t =
      S.rootEquiv R i (-1) (by decide) (-t) * S.weylEquiv R i 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro μ r
  simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply, LinearEquiv.coe_coe]
  rcases S.minuscule i μ with h | h | h
  all_goals
    simp [rootEquiv, transvection_apply, step_single, h, map_add, map_smul,
      S.weylEquiv_single_neg, S.weylEquiv_single_pos, S.weylEquiv_single_zero,
      S.pairing_reflection, S.involutive, Finsupp.smul_single,
      smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, add_comm]

variable [Fintype Ω] [DecidableEq Ω]

theorem weylMatrixUnit_one_conjugate_lowering (i : I) (t : R) :
    S.weylMatrixUnit R i 1 * S.rootMatrixUnit R i 1 (by decide) t *
      (S.weylMatrixUnit R i 1)⁻¹ = S.rootMatrixUnit R i (-1) (by decide) (-t) := by
  have h := congrArg (equivMatrixHom R) (S.weylEquiv_one_mul_lowering R i t)
  have hmul : S.weylMatrixUnit R i 1 * S.rootMatrixUnit R i 1 (by decide) t =
      S.rootMatrixUnit R i (-1) (by decide) (-t) * S.weylMatrixUnit R i 1 := by
    simpa only [map_mul, equivMatrixHom_weyl, equivMatrixHom_root] using h
  rw [hmul, mul_assoc, mul_inv_cancel, mul_one]

end Atlas.Chevalley.Integral.Minuscule.Strings
