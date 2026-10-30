import Atlas.LinearGroups.ReeF4.TailRhoCarrierIdentities

/-! Separate group-level layer of the rho normalizer proof.
The prior statements and proof bodies are preserved; verification is recorded separately. -/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem rho_positiveTailShort_conjugate {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 3) (a b : F) :
    weylRhoModel m * positiveShortFactor hcard k.succ a b * (weylRhoModel m)⁻¹ =
      positiveShortFactor hcard (Fin.rev k).succ a b := by
  have hi : weylRhoModel m * positiveShortFactor hcard k.succ a b =
      positiveShortFactor hcard (Fin.rev k).succ a b * weylRhoModel m := by
    apply model_ext_of_carrier_action
    intro w
    simp only [modelProduct_apply, positiveShortFactor,
      alternatingShortFactor_pair_val, tailRhoCarrier_model]
    exact tailRhoCarrier_short m k a b w.val
  rw [hi, mul_assoc, mul_inv_cancel, mul_one]

theorem rho_positiveLong_conjugate {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) (u : F) :
    weylRhoModel m * positiveLongFactor hcard k u * (weylRhoModel m)⁻¹ =
      positiveLongFactor hcard (Fin.rev k) u := by
  have hi : weylRhoModel m * positiveLongFactor hcard k u =
      positiveLongFactor hcard (Fin.rev k) u * weylRhoModel m := by
    apply model_ext_of_carrier_action
    intro w
    simp only [modelProduct_apply, positiveLongFactor,
      alternatingLongFactor_val, tailRhoCarrier_model]
    exact tailRhoCarrier_long m k u w.val
  rw [hi, mul_assoc, mul_inv_cancel, mul_one]

end Atlas.ReeF4
