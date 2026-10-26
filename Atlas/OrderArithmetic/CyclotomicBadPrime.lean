import Atlas.OrderArithmetic.CyclotomicPrimitive
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.FieldTheory.Finite.Basic

namespace Atlas.OrderArithmetic
open Polynomial

/-- Reduction of a cyclotomic index at the characteristic prime determines the
exact remaining order. This statement also allows exponent zero. -/
theorem cyclotomic_prime_power_index_order {a l k m : ℕ} (hl : l.Prime)
    (hm : ¬ l ∣ m)
    (hdiv : l ∣ ((cyclotomic (l ^ k * m) ℤ).eval (a : ℤ)).natAbs) :
    orderOf (a : ZMod l) = m ∧ m ∣ l - 1 := by
  letI : Fact l.Prime := ⟨hl⟩
  letI : NeZero (m : ZMod l) := NeZero.of_not_dvd (ZMod l) hm
  have hmpos : 0 < m := by
    by_contra hn
    have he : m = 0 := by omega
    exact hm (he ▸ dvd_zero l)
  have hroot : IsRoot (cyclotomic (l ^ k * m) (ZMod l))
      (Nat.castRingHom (ZMod l) a) := by
    have hc : ((a : ℤ) : ZMod l) = ↑(Int.castRingHom (ZMod l) a) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int (l ^ k * m) (ZMod l), eval_map,
      Nat.coe_castRingHom, ← Int.cast_natCast, hc, eval₂_hom, Int.coe_castRingHom,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact_mod_cast hdiv
  have hprim : IsPrimitiveRoot (a : ZMod l) m :=
    isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
  have horder : orderOf (a : ZMod l) = m := hprim.eq_orderOf.symm
  refine ⟨horder, ?_⟩
  rw [← horder]
  exact ZMod.orderOf_dvd_card_sub_one (hprim.isUnit (by omega)).ne_zero

/-- Every prime factor of the cyclotomic index is at most the characteristic
prime when that prime divides the evaluated polynomial at its own prime-power
index part. No valuation-one assertion is made here. -/
theorem cyclotomic_prime_power_index_prime_bound {a l k m r : ℕ} (hl : l.Prime)
    (hm : ¬ l ∣ m)
    (hdiv : l ∣ ((cyclotomic (l ^ k * m) ℤ).eval (a : ℤ)).natAbs)
    (hr : r.Prime) (hrdiv : r ∣ l ^ k * m) : r ≤ l := by
  obtain ⟨_, hml⟩ := cyclotomic_prime_power_index_order hl hm hdiv
  rcases hr.dvd_mul.mp hrdiv with hpow | hrest
  · have he : r = l := (Nat.prime_dvd_prime_iff_eq hr hl).mp (hr.dvd_of_dvd_pow hpow)
    omega
  · have hle : r ≤ l - 1 := Nat.le_of_dvd (by have := hl.two_le; omega) (hrest.trans hml)
    omega

end Atlas.OrderArithmetic
