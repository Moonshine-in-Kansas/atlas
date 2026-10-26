import Atlas.GroupTheory.PrimeDegree
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! A small faithful five-point action forces the full affine group order.
Only Lagrange, Sylow, and the prime-degree normalizer bound enter the proof. -/

namespace Atlas.GroupTheory

/-- A faithful transitive five-point group whose order divides 20480 and which
contains an element of order four has order twenty. -/
theorem card_twenty_of_faithful_five_point_action {G X : Type*}
    [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X]
    (hX : Nat.card X = 5) (hdiv : Nat.card G ∣ 20480)
    (g : G) (hg : orderOf g = 4) : Nat.card G = 20 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Nonempty X := (Nat.card_pos_iff.mp (hX ▸ (by decide : 0 < 5))).1
  let x : X := Classical.choice inferInstance
  have hperm := Subgroup.card_dvd_of_injective (MulAction.toPermHom G X)
    MulAction.toPerm_injective
  rw [Nat.card_perm, hX] at hperm
  have hd40 : Nat.card G ∣ 40 := by
    have hd := Nat.dvd_gcd hperm hdiv
    norm_num at hd
    exact hd
  have hd5 : 5 ∣ Nat.card G := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)
    rw [Nat.card_prod] at hc
    have ho : Nat.card (MulAction.orbit G x) = 5 := by
      rw [MulAction.orbit_eq_univ]
      simpa using hX
    rw [ho] at hc
    exact ⟨_,hc.symm⟩
  have hsq : ¬5^2 ∣ Nat.card G := by
    intro h
    exact (by decide : ¬5^2 ∣ (40 : ℕ)) (h.trans hd40)
  let P : Sylow 5 G := Classical.choice inferInstance
  have hP : Nat.card P = 5 := sylow_card_prime 5 hd5 hsq P
  haveI : MulAction.IsPretransitive P X :=
    prime_subgroup_pretransitive (G := G) 5 hX (P : Subgroup G) hP
  obtain ⟨s,hs,hnorm,hfactor⟩ := sylow_normalizer_factor 5 P hP
  have hbound := prime_normalizer_card_bound (G := G) P x 5 hP hX
  change Nat.card (Subgroup.normalizer (P : Set G)) ≤ 5*(5-1) at hbound
  rw [hnorm] at hbound
  have hcountdiv : Nat.card (Sylow 5 G) ∣ 8 := by
    have hmul : 5 * Nat.card (Sylow 5 G) ∣ Nat.card G :=
      ⟨s, by nlinarith [hfactor]⟩
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 5)).mp
      (show 5 * Nat.card (Sylow 5 G) ∣ 5 * 8 from hmul.trans hd40)
  have hmod : Nat.card (Sylow 5 G) % 5 = 1 := by
    simpa only [Nat.ModEq, Nat.reduceMod] using card_sylow_modEq_one 5 G
  have hcountle : Nat.card (Sylow 5 G) ≤ 8 := Nat.le_of_dvd (by decide) hcountdiv
  have hcount : Nat.card (Sylow 5 G) = 1 := by
    have halt : Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by omega
    rcases halt with h | h
    · exact h
    · rw [h] at hcountdiv
      exact False.elim ((by decide : ¬(6 : ℕ) ∣ 8) hcountdiv)
  have hle : Nat.card G ≤ 20 := by
    rw [hfactor,hcount,mul_one]
    exact hbound
  have hd4 : 4 ∣ Nat.card G := hg ▸ orderOf_dvd_natCard g
  have hd20 : 20 ∣ Nat.card G :=
    (by decide : Nat.Coprime 5 4).mul_dvd_of_dvd_of_dvd hd5 hd4
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hd20)

/-- Every permutation of a five-element set has order dividing sixty. The
proof uses the cycle-length least common multiple, not a permutation certificate. -/
theorem perm_five_pow_sixty {X : Type*} [Finite X]
    (hX : Nat.card X = 5) (σ : Equiv.Perm X) : σ ^ 60 = 1 := by
  classical
  letI := Fintype.ofFinite X
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro c hc
  have hlo := Equiv.Perm.two_le_of_mem_cycleType hc
  have hhi := (Multiset.le_sum_of_mem hc).trans σ.sum_cycleType_le
  rw [← Nat.card_eq_fintype_card, hX] at hhi
  interval_cases c <;> norm_num

end Atlas.GroupTheory

