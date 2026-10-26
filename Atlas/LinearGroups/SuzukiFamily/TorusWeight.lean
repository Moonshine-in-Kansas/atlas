import Atlas.LinearGroups.SuzukiFamily.Twist

/-! The nontrivial torus weight is bijective on actual field units. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem weight_eq_one (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (t : F)
    (ht : t^2 * theta F m t = 1) : t = 1 := by
  have he := congrArg (theta F m) ht
  rw [map_mul,map_pow,theta_square hcard,map_one] at he
  have hs : theta F m t = 1 := calc
    theta F m t = theta F m t * (t^2 * theta F m t) := by rw [ht,mul_one]
    _ = (theta F m t)^2*t^2 := by ring
    _ = 1 := he
  apply (theta F m).injective
  simpa only [map_one] using hs

def torusWeight (m : ℕ) : Fˣ →* Fˣ where
  toFun t := t^2 * Units.map (theta F m).toMonoidHom t
  map_one' := by simp
  map_mul' a b := by simp [mul_pow]; ac_rfl

theorem torusWeight_injective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (torusWeight (F := F) m) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro t ht
  apply Units.ext
  apply weight_eq_one m hcard
  exact congrArg Units.val ht

theorem torusWeight_bijective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Bijective (torusWeight (F := F) m) :=
  Finite.injective_iff_bijective.mp (torusWeight_injective m hcard)
end Atlas.SuzukiFamily
