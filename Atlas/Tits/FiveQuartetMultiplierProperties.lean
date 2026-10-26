import Atlas.Tits.FiveQuartetMultiplier
import Atlas.GroupTheory.CyclicAutomorphismExponent

namespace Atlas.Tits

/-- The actual geometric action has the required 1024-element kernel. -/
theorem fiveQuartetHom_kernel_order : Nat.card fiveQuartetHom.ker = 1024 := by
  have h := fiveQuartetHom.ker.card_mul_index
  rw [Subgroup.index_ker] at h
  change Nat.card fiveQuartetHom.ker * Nat.card fiveQuartetImage = Nat.card pairStabilizer at h
  rw [fiveQuartetImage_order, cardPairStabilizer] at h
  omega

/-- The actual multiplier acts by its exponent on the normal cyclic subgroup. -/
theorem fiveQuartetImageMultiplier_exponent (g : fiveQuartetImage)
    (x : fiveQuartetSylow) :
    fiveQuartetConjugation g x = x ^ (fiveQuartetImageMultiplier g : ZMod 5).val := by
  letI : NeZero (Nat.card fiveQuartetSylow) := ⟨by rw [fiveQuartetSylow_order]; decide⟩
  have h := Atlas.GroupTheory.cyclic_automorphism_exponent (fiveQuartetConjugation g) x
  have hv : (fiveQuartetImageMultiplier g : ZMod 5).val =
      (((IsCyclic.mulAutMulEquiv fiveQuartetSylow (fiveQuartetConjugation g)) :
        ZMod (Nat.card fiveQuartetSylow))).val := by
    exact ZMod.ringEquivCongr_val fiveQuartetSylow_order _
  rwa [hv]

/-- Replacing a generator leaves the same exponent: in fact the formula holds
 simultaneously for any two elements of the actual cyclic group. -/
theorem fiveQuartetMultiplier_generator_independent (g : pairStabilizer)
    (x y : fiveQuartetSylow) :
    fiveQuartetConjugation (fiveQuartetHom.rangeRestrict g) x =
      x ^ (fiveQuartetMultiplier g : ZMod 5).val ∧
    fiveQuartetConjugation (fiveQuartetHom.rangeRestrict g) y =
      y ^ (fiveQuartetMultiplier g : ZMod 5).val :=
  ⟨fiveQuartetImageMultiplier_exponent _ x, fiveQuartetImageMultiplier_exponent _ y⟩

end Atlas.Tits
