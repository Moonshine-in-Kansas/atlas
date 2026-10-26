import Atlas.OrderArithmetic.FixedComparisons

namespace Atlas.OrderArithmetic

theorem alternating_not_prime {n : ℕ} (hn : 5 ≤ n) : ¬ (order (.alternating n)).Prime := by
  have hfac : 120 ≤ n.factorial := by simpa [Nat.factorial] using Nat.factorial_le hn
  have hd : 3 ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
  rw [← alternating_double (by omega : 2 ≤ n)] at hd
  have hthree : 3 ∣ n.factorial / 2 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr (by norm_num)).dvd_of_dvd_mul_left hd
  intro hp
  change (n.factorial / 2).Prime at hp
  rcases hp.eq_one_or_self_of_dvd 3 hthree with h | h <;> omega

theorem cyclic_ne_alternating {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n) :
    order (.cyclic p) ≠ order (.alternating n) := by
  intro h
  change p = order (.alternating n) at h
  exact alternating_not_prime hn (h ▸ hp)

theorem cyclic_order_injective {p q : ℕ} (h : order (.cyclic p) = order (.cyclic q)) : p = q := h

end Atlas.OrderArithmetic
