import Atlas.Conway.LeechPrimeOrder
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

theorem leech_subgroup_prime_divisor_le (H : Subgroup LeechIsometryGroup)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card H) : p ≤ 23 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' p hd
  apply leech_prime_order_le g.val p hp
  simpa using hg

theorem leech_orbit_card_dvd (H : Subgroup LeechIsometryGroup)
    {X : Type*} [MulAction H X] (x : X) : Nat.card (MulAction.orbit H x) ∣ Nat.card H := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod] at he
  exact ⟨Nat.card (MulAction.stabilizer H x),he.symm⟩

theorem leech_orbit_prime_divisor_le (H : Subgroup LeechIsometryGroup)
    {X : Type*} [MulAction H X] (x : X) (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Nat.card (MulAction.orbit H x)) : p ≤ 23 :=
  leech_subgroup_prime_divisor_le H p hp (hd.trans (leech_orbit_card_dvd H x))

theorem leech_forbidden_orbit_sizes (H : Subgroup LeechIsometryGroup)
    {X : Type*} [MulAction H X] (x : X) :
    Nat.card (MulAction.orbit H x) ≠ 98256 ∧
    Nat.card (MulAction.orbit H x) ≠ 99408 ∧
    Nat.card (MulAction.orbit H x) ≠ 926 := by
  refine ⟨?_,?_,?_⟩
  · intro he
    have h := leech_orbit_prime_divisor_le H x 89 (by norm_num) (by rw [he]; norm_num)
    omega
  · intro he
    have h := leech_orbit_prime_divisor_le H x 109 (by norm_num) (by rw [he]; norm_num)
    omega
  · intro he
    have h := leech_orbit_prime_divisor_le H x 463 (by norm_num) (by rw [he]; norm_num)
    omega

end Atlas.Conway
