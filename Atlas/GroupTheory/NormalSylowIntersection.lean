import Mathlib.GroupTheory.Sylow

noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

/-- With Sylow subgroups of prime order, a normal subgroup containing that prime meets
every subgroup whose order contains the same prime. The proof uses Sylow conjugacy. -/
theorem normal_meets_subgroup_of_prime_sylow (G : Type*) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hSylow : ∀ P : Sylow p G, Nat.card P = p)
    (N M : Subgroup G) [N.Normal] (hN : p ∣ Nat.card N) (hM : p ∣ Nat.card M) :
    ∃ x : G, x ∈ N ∧ x ∈ M ∧ x ≠ 1 := by
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := N) p hN
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := M) p hM
  have huG : orderOf (u.val : G) = p := (Subgroup.orderOf_coe u).trans hu
  have hvG : orderOf (v.val : G) = p := (Subgroup.orderOf_coe v).trans hv
  have hcu : Nat.card (Subgroup.zpowers (u.val : G)) = p := by rw [Nat.card_zpowers,huG]
  have hcv : Nat.card (Subgroup.zpowers (v.val : G)) = p := by rw [Nat.card_zpowers,hvG]
  have hpu : IsPGroup p (Subgroup.zpowers (u.val : G)) := IsPGroup.of_card (n := 1) (by simpa using hcu)
  have hpv : IsPGroup p (Subgroup.zpowers (v.val : G)) := IsPGroup.of_card (n := 1) (by simpa using hcv)
  obtain ⟨P,hP⟩ := hpu.exists_le_sylow
  obtain ⟨Q,hQ⟩ := hpv.exists_le_sylow
  have heP : Subgroup.zpowers (u.val : G) = P.toSubgroup :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hcu,hSylow P])
  have heQ : Subgroup.zpowers (v.val : G) = Q.toSubgroup :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hcv,hSylow Q])
  have hPN : P.toSubgroup ≤ N := by
    rw [← heP]
    exact Subgroup.zpowers_le.mpr u.prop
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  have hQN : Q.toSubgroup ≤ N := by
    rw [← hg]
    intro x hx
    change x ∈ (MulAut.conj g) • (P : Set G) at hx
    obtain ⟨y,hy,he⟩ := hx
    have hn := (inferInstance : N.Normal).conj_mem y (hPN hy) g
    exact he ▸ hn
  refine ⟨v.val,hQN (heQ ▸ Subgroup.mem_zpowers v.val),v.prop,?_⟩
  intro he
  rw [he,orderOf_one] at hvG
  exact (Fact.out : p.Prime).ne_one hvG.symm

end Atlas.GroupTheory
