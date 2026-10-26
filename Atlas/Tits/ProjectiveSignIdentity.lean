import Atlas.Tits.LocalSignIdentity

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
open scoped commutatorElement

noncomputable def codeToRudvalis : codeGroup →* RudvalisGroup :=
  (QuotientGroup.mk' gaussianScalarSubgroup).comp codeGaussianHom

theorem codeToRudvalis_I : codeToRudvalis codeI = 1 := by
  change QuotientGroup.mk' gaussianScalarSubgroup (codeGaussianHom codeI) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (codeGaussian_scalar_iff codeI).mpr (Subgroup.mem_zpowers _)

/-- The scalar correction in the full operator identity disappears only
under the actual scalar quotient homomorphism. -/
theorem projective_double_commutator_sign :
    ⁅⁅codeToRudvalis coupleCodeD ^ 4, codeToRudvalis codeV⁆, codeToRudvalis codeV⁆ =
      codeToRudvalis (seedARowSign (binaryLabel 4)) := by
  have h := congrArg codeToRudvalis code_double_commutator_sign
  simpa only [map_commutatorElement, map_pow, map_mul, codeToRudvalis_I,
    one_pow, one_mul] using h

end Atlas.Tits
