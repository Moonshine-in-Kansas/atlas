import Atlas.Sporadic.Janko1.PQComplement
import Atlas.Sporadic.Janko1.SignNormalizer

/-!
Source-only local checkpoint for the existing H = closure {P,Q,R}.
The actual sign subgroup and actual P,Q subgroup give a unique factorization,
then a unique 8 × 7 × 3 coordinate form. Its cardinality is a consequence.
The sign-conjugation/normalizer prerequisites and this candidate remain
uncompiled at this handoff. No order or simplicity assertion about J1 is used.
-/
namespace Atlas.Janko1
open scoped Pointwise

theorem sign_pq_disjoint : Disjoint signSubgroup pqSubgroup := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [card_signSubgroup, card_pqSubgroup]
  decide

/-- Equality follows from the specified generators and containment, before counting H. -/
theorem H_eq_signSubgroup_sup_pqSubgroup : H = signSubgroup ⊔ pqSubgroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_sup_right P_mem_pqSubgroup
    · exact Subgroup.mem_sup_right Q_mem_pqSubgroup
    · exact Subgroup.mem_sup_left R_mem_signSubgroup
  · exact sup_le signSubgroup_le_H pqSubgroup_le_H

theorem pqSubgroup_le_sign_normalizer :
    pqSubgroup ≤ Subgroup.normalizer (signSubgroup : Set (G2.Model Field)) :=
  pqSubgroup_le_H.trans H_le_signSubgroup_normalizer

/-- The forward map multiplies the two existing octonion automorphisms. -/
def hMultiply (x : signSubgroup × pqSubgroup) : H :=
  ⟨(x.1 : G2.Model Field) * (x.2 : G2.Model Field),
    H.mul_mem (signSubgroup_le_H x.1.property) (pqSubgroup_le_H x.2.property)⟩

theorem hMultiply_bijective : Function.Bijective hMultiply := by
  constructor
  · intro x y hxy
    apply Subgroup.mul_injective_of_disjoint sign_pq_disjoint
    exact congrArg (fun z : H => (z : G2.Model Field)) hxy
  · intro g
    have hg : (g : G2.Model Field) ∈
        (signSubgroup : Set (G2.Model Field)) * (pqSubgroup : Set (G2.Model Field)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left signSubgroup pqSubgroup
        pqSubgroup_le_sign_normalizer]
      rw [← H_eq_signSubgroup_sup_pqSubgroup]
      exact g.property
    obtain ⟨e, he, c, hc, hec⟩ := hg
    exact ⟨(⟨e, he⟩, ⟨c, hc⟩), Subtype.ext hec⟩

noncomputable def hProductEquiv : (signSubgroup × pqSubgroup) ≃ H :=
  Equiv.ofBijective hMultiply hMultiply_bijective

noncomputable def hNormalFormEquiv : (SignParameters × (Fin 7 × Fin 3)) ≃ H :=
  (Equiv.prodCongr (Multiplicative.ofAdd.trans signSubgroupEquiv.toEquiv)
    pqNormalFormEquiv).trans hProductEquiv

theorem hNormalFormEquiv_apply (t : SignParameters × (Fin 7 × Fin 3)) :
    (hNormalFormEquiv t : G2.Model Field) =
      signElement t.1 * P ^ t.2.1.val * Q ^ t.2.2.val := by
  change signElement t.1 * (P ^ t.2.1.val * Q ^ t.2.2.val) = _
  exact (mul_assoc _ _ _).symm

theorem H_normal_form (g : H) :
    ∃! t : SignParameters × (Fin 7 × Fin 3),
      signElement t.1 * P ^ t.2.1.val * Q ^ t.2.2.val = (g : G2.Model Field) := by
  refine ⟨hNormalFormEquiv.symm g, ?_, ?_⟩
  · simpa only [hNormalFormEquiv_apply] using
      congrArg (fun z : H => (z : G2.Model Field)) (hNormalFormEquiv.apply_symm_apply g)
  · intro t ht
    apply hNormalFormEquiv.injective
    have ht' : hNormalFormEquiv t = g := Subtype.ext (by
      simpa only [hNormalFormEquiv_apply] using ht)
    exact ht'.trans (hNormalFormEquiv.apply_symm_apply g).symm

theorem card_H : Nat.card H = 168 := by
  calc
    Nat.card H = Nat.card (signSubgroup × pqSubgroup) :=
      (Nat.card_congr hProductEquiv).symm
    _ = 168 := by rw [Nat.card_prod, card_signSubgroup, card_pqSubgroup]

end Atlas.Janko1
