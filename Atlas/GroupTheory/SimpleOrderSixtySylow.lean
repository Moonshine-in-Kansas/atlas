import Atlas.GroupTheory.DisjointSubgroupCounting
import Atlas.GroupTheory.SmallIndexSimple
import Atlas.GroupTheory.CenterSimpleQuotient
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance simpleOrderSixtySylowPrime1 : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance simpleOrderSixtySylowPrime2 : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem simple_sixty_proper_index_ge_five (hG : Nat.card G=60) (H : Subgroup G) (hH : H≠⊤) :
    5≤H.index := by
  by_contra hn
  have hh : H.index.factorial < Nat.card G := by
    have hm := Nat.factorial_le (show H.index≤4 by omega)
    rw [hG]
    exact lt_of_le_of_lt hm (by decide)
  exact hH (subgroup_eq_top_of_index_factorial_lt H hh)

theorem sylow_two_card_of_sixty (hG : Nat.card G=60) (P : Sylow 2 G) : Nat.card P=4 := by
  rw [Sylow.card_eq_multiplicity,hG]
  rw [show 60 = 2^2*15 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime (2^2) 15),
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣15)]
  norm_num

theorem sylow_five_card_of_sixty (hG : Nat.card G=60) (P : Sylow 5 G) : Nat.card P=5 := by
  rw [Sylow.card_eq_multiplicity,hG]
  rw [show 60 = 5*12 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 5 12),
    (by decide : Nat.Prime 5).factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣12)]
  norm_num

private theorem normalizer_ne_top_of_card {p : ℕ} (hG : Nat.card G=60) (P : Sylow p G)
    (hP : 1<Nat.card P) (hP' : Nat.card P<60) : Subgroup.normalizer (P : Set G)≠⊤ := by
  intro hn
  haveI : P.toSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  rcases (inferInstance : P.toSubgroup.Normal).eq_bot_or_eq_top with hp|hp
  · have h := congrArg (fun H : Subgroup G => Nat.card H) hp
    simp only [Subgroup.card_bot] at h
    omega
  · have h := congrArg (fun H : Subgroup G => Nat.card H) hp
    simp only [Subgroup.card_top,hG] at h
    omega

theorem sylow_two_count_of_simple_sixty (hG : Nat.card G=60) :
    Nat.card (Sylow 2 G)=5 ∨ Nat.card (Sylow 2 G)=15 := by
  let P : Sylow 2 G := Classical.choice inferInstance
  have hp := sylow_two_card_of_sixty hG P
  have hi : P.toSubgroup.index=15 := by
    have hh := P.toSubgroup.card_mul_index
    rw [hp,hG] at hh
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hl : 5≤Nat.card (Sylow 2 G) := by
    rw [Sylow.card_eq_index_normalizer P]
    exact simple_sixty_proper_index_ge_five hG _ (normalizer_ne_top_of_card hG P (by omega) (by omega))
  have hu := Nat.le_of_dvd (by decide : 0<15) hd
  interval_cases hc : Nat.card (Sylow 2 G) <;> omega

theorem sylow_five_count_of_simple_sixty (hG : Nat.card G=60) : Nat.card (Sylow 5 G)=6 := by
  let P : Sylow 5 G := Classical.choice inferInstance
  have hp := sylow_five_card_of_sixty hG P
  have hi : P.toSubgroup.index=12 := by
    have hh := P.toSubgroup.card_mul_index
    rw [hp,hG] at hh
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hl : 5≤Nat.card (Sylow 5 G) := by
    rw [Sylow.card_eq_index_normalizer P]
    exact simple_sixty_proper_index_ge_five hG _ (normalizer_ne_top_of_card hG P (by omega) (by omega))
  have hu := Nat.le_of_dvd (by decide : 0<12) hd
  have hm : Nat.card (Sylow 5 G)%5=1 := card_sylow_modEq_one 5 G
  interval_cases hc : Nat.card (Sylow 5 G) <;> omega

end Atlas.GroupTheory

namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance simpleOrderSixtySylowPrime3 : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem simple_sixty_index_five_of_sylow_intersection (hG : Nat.card G=60)
    (hn : ¬IsMulCommutative G) (P Q : Sylow 2 G) (hPQ : P≠Q)
    (t : G) (ht : t≠1) (htP : t∈P) (htQ : t∈Q) :
    ∃H : Subgroup G,H.index=5 := by
  let C := Subgroup.centralizer ({t} : Set G)
  have hin (R : Sylow 2 G) (htR : t∈R) : R.toSubgroup≤C := by
    letI := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (show Nat.card R=2^2 from sylow_two_card_of_sixty hG R)
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have hy' : y=t := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val ((inferInstance : IsMulCommutative R).is_comm.comm (⟨t,htR⟩ : R) ⟨x,hx⟩)
  have hp := hin P htP
  have hq := hin Q htQ
  have hproper : C≠⊤ := by
    intro hc
    have hz : t∈Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp hc) (Set.mem_singleton t)
    rw [center_eq_bot_of_simple_nonabelian G hn] at hz
    exact ht hz
  have hd : 4∣Nat.card C := by
    simpa [sylow_two_card_of_sixty hG P] using Subgroup.card_dvd_of_le hp
  have hc4 : 4<Nat.card C := by
    have hh := Nat.le_of_dvd (Nat.card_pos (α := C)) hd
    by_contra hlt
    have he : Nat.card C=4 := by omega
    have hPC : P.toSubgroup=C := Subgroup.eq_of_le_of_card_ge hp (by rw [he,sylow_two_card_of_sixty hG P])
    have hQC : Q.toSubgroup=C := Subgroup.eq_of_le_of_card_ge hq (by rw [he,sylow_two_card_of_sixty hG Q])
    exact hPQ (Sylow.ext (hPC.trans hQC.symm))
  have hindex := simple_sixty_proper_index_ge_five hG C hproper
  have hprod := C.card_mul_index
  rw [hG] at hprod
  have hupper : Nat.card C≤12 := by nlinarith
  have hdiv := C.card_subgroup_dvd_card
  rw [hG] at hdiv
  have hcard : Nat.card C=12 := by
    interval_cases hc : Nat.card C <;> omega
  refine ⟨C,?_⟩
  rw [hcard] at hprod
  omega

end Atlas.GroupTheory

namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance simpleOrderSixtySylowPrime4 : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance simpleOrderSixtySylowPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- An elementary Sylow-counting construction of a subgroup of index five. -/
theorem subgroup_index_five_of_simple_card_sixty (hG : Nat.card G=60) (hn : ¬IsMulCommutative G) :
    ∃H : Subgroup G,H.index=5 := by
  classical
  rcases sylow_two_count_of_simple_sixty hG with hc|hc
  · let P : Sylow 2 G := Classical.choice inferInstance
    exact ⟨Subgroup.normalizer (P : Set G),(Sylow.card_eq_index_normalizer P).symm.trans hc⟩
  · by_cases hd : Pairwise (fun P Q : Sylow 2 G => Disjoint P.toSubgroup Q.toSubgroup)
    · letI := Fintype.ofFinite (Sylow 2 G)
      letI := Fintype.ofFinite (Sylow 5 G)
      let H : Sylow 2 G ⊕ Sylow 5 G → Subgroup G := Sum.elim (fun P => P.toSubgroup) (fun P => P.toSubgroup)
      have hH : Pairwise (fun i j => Disjoint (H i) (H j)) := by
        intro i j hij
        cases i with
        | inl P =>
          cases j with
          | inl Q => exact hd (fun h => hij (congrArg Sum.inl h))
          | inr Q => exact IsPGroup.disjoint_of_ne 2 5 (by decide) P.toSubgroup Q.toSubgroup P.isPGroup' Q.isPGroup'
        | inr P =>
          cases j with
          | inl Q => exact (IsPGroup.disjoint_of_ne 2 5 (by decide) Q.toSubgroup P.toSubgroup Q.isPGroup' P.isPGroup').symm
          | inr Q =>
            exact subgroups_prime_card_disjoint (G := G) (by decide : Nat.Prime 5)
              P.toSubgroup Q.toSubgroup (sylow_five_card_of_sixty hG P) (sylow_five_card_of_sixty hG Q)
              (fun h => hij (congrArg Sum.inr (Sylow.ext h)))
      have hb := disjoint_subgroup_nonidentity_card_bound H hH
      have h5 := sylow_five_count_of_simple_sixty hG
      simp [H,Fintype.sum_sum_type,sylow_two_card_of_sixty hG,sylow_five_card_of_sixty hG,
        ←Nat.card_eq_fintype_card,hc,h5,hG] at hb
    · simp only [Pairwise] at hd
      push_neg at hd
      obtain ⟨P,Q,hPQ,hd⟩ := hd
      rw [Subgroup.disjoint_def] at hd
      push_neg at hd
      obtain ⟨t,htP,htQ,ht⟩ := hd
      exact simple_sixty_index_five_of_sylow_intersection hG hn P Q hPQ t ht htP htQ

end Atlas.GroupTheory
