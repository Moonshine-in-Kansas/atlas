import Atlas.OrderArithmetic.PrimitiveDivisorBounds
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

namespace Atlas.OrderArithmetic
open Polynomial

/-- A prime factor of an evaluated cyclotomic polynomial is primitive whenever
it does not divide the cyclotomic index. This does not assert that such a prime
factor exists. -/
theorem cyclotomic_prime_factor_primitive_of_not_dvd_index {a n l : ℕ}
    (ha : 2 ≤ a) (hn : 0 < n) (hl : l.Prime)
    (hdiv : l ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs) (hind : ¬ l ∣ n) :
    PrimitiveDivisor a n l := by
  letI : Fact l.Prime := ⟨hl⟩
  have hroot : IsRoot (cyclotomic n (ZMod l)) (Nat.castRingHom (ZMod l) a) := by
    have hc : ((a : ℤ) : ZMod l) = ↑(Int.castRingHom (ZMod l) a) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod l), eval_map, Nat.coe_castRingHom,
      ← Int.cast_natCast, hc, eval₂_hom, Int.coe_castRingHom,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact_mod_cast hdiv
  letI : NeZero (n : ZMod l) := NeZero.of_not_dvd (ZMod l) hind
  have hprim : IsPrimitiveRoot (a : ZMod l) n := isRoot_cyclotomic_iff.mp hroot
  have hiff : ∀ j : ℕ, (a : ZMod l) ^ j = 1 ↔ l ∣ a ^ j - 1 := by
    intro j
    rw [← ZMod.natCast_eq_zero_iff (a ^ j - 1) l,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 1 ≤ a)),
      Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  refine ⟨hn, hl, (hiff n).mp hprim.pow_eq_one, ?_⟩
  intro j hj hjn hd
  exact hprim.pow_ne_one_of_pos_of_lt (by omega) hjn ((hiff j).mpr hd)

end Atlas.OrderArithmetic
