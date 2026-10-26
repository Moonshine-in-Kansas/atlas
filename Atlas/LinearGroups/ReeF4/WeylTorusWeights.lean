import Atlas.LinearGroups.ReeF4.WeylStarData
import Atlas.LinearGroups.ReeF4.TorusFieldWeights

/-! The concrete Weyl action on the source's two torus parameters. -/
namespace Atlas.ReeF4

private theorem sigma_character_indices : ∀ r : ShortRootLabel,
    torusConstantExponents (weylRootImage 1 r) = (torusConstantExponents r).swap ∧
    torusThetaExponents (weylRootImage 1 r) = (torusThetaExponents r).swap := by decide

private theorem rho_character_indices : ∀ r : ShortRootLabel,
    torusConstantExponents (weylRootImage 0 r) =
      ((torusConstantExponents r).1 + 2 * (torusThetaExponents r).2,
        -(torusConstantExponents r).2) ∧
    torusThetaExponents (weylRootImage 0 r) =
      ((torusConstantExponents r).2 + (torusThetaExponents r).1,
        -(torusThetaExponents r).2) := by decide

variable {G : Type*} [CommGroup G]

theorem twistedTorusWeight_sigma (τ : G →* G) (a b : G) (r : ShortRootLabel) :
    twistedTorusWeight τ a b (weylRootImage 1 r) = twistedTorusWeight τ b a r := by
  obtain ⟨hc, ht⟩ := sigma_character_indices r
  simp only [twistedTorusWeight, hc, ht, torusCharacter, Prod.fst_swap, Prod.snd_swap]
  ac_rfl

private theorem rho_character_identity (a b x y : G) (c d e f : ℤ) :
    a ^ (c + 2*f) * b ^ (-d) * (x ^ (d+e) * y ^ (-f)) =
      a ^ c * (x * b⁻¹) ^ d * (x ^ e * ((a*a) * y⁻¹) ^ f) := by
  simp only [two_mul, zpow_add, zpow_neg, mul_zpow, inv_zpow]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem twistedTorusWeight_rho (τ : G →* G) (a b : G)
    (ha : τ (τ a) = a^2) (r : ShortRootLabel) :
    twistedTorusWeight τ a b (weylRootImage 0 r) =
      twistedTorusWeight τ a (τ a * b⁻¹) r := by
  obtain ⟨hc, ht⟩ := rho_character_indices r
  simpa only [twistedTorusWeight, hc, ht, torusCharacter, map_mul, map_inv, ha,
    pow_two] using
    rho_character_identity a b (τ a) (τ b)
      (torusConstantExponents r).1 (torusConstantExponents r).2
      (torusThetaExponents r).1 (torusThetaExponents r).2

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem torusWeight_sigma (m : ℕ) (a b : Fˣ) (r : ShortRootLabel) :
    torusWeight m a b (weylRootImage 1 r) = torusWeight m b a r := by
  rw [torusWeight_eq_twisted m (thetaUnits m) a b (thetaUnits_apply m a) (thetaUnits_apply m b),
    torusWeight_eq_twisted m (thetaUnits m) b a (thetaUnits_apply m b) (thetaUnits_apply m a)]
  exact twistedTorusWeight_sigma (thetaUnits m) a b r

theorem torusWeight_rho {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) (r : ShortRootLabel) :
    torusWeight m a b (weylRootImage 0 r) =
      torusWeight m a (thetaUnits m a * b⁻¹) r := by
  rw [torusWeight_eq_twisted m (thetaUnits m) a b (thetaUnits_apply m a) (thetaUnits_apply m b),
    torusWeight_eq_twisted m (thetaUnits m) a (thetaUnits m a * b⁻¹)
      (thetaUnits_apply m a) (thetaUnits_apply m _)]
  exact twistedTorusWeight_rho (thetaUnits m) a b (thetaUnits_square hcard a) r

end Atlas.ReeF4
