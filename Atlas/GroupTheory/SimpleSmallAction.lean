import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Prime.Factorial

noncomputable section
namespace Atlas.GroupTheory
open MulAction

/-- A nontrivial orbit of a finite simple group has size at least every prime divisor of its order. -/
theorem simple_orbit_prime_bound (G X : Type*) [Group G] [Finite G] [Finite X]
    [MulAction G X] [IsSimpleGroup G] (p : ℕ) (hp : p.Prime) (hpg : p ∣ Nat.card G)
    (x : X) (hx : ∃ g : G, g • x ≠ x) : p ≤ Nat.card (orbit G x) := by
  classical
  letI : Fintype (orbit G x) := Fintype.ofFinite _
  let f := MulAction.toPermHom G (orbit G x)
  have hi : Function.Injective f := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff f).mp hbot
    · obtain ⟨g,hg⟩ := hx
      have h : f g = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [htop]; trivial
      have he := congrArg (fun q : Equiv.Perm (orbit G x) =>
        (q ⟨x,mem_orbit_self x⟩).val) h
      exact False.elim (hg he)
  have hd := hpg.trans (Subgroup.card_dvd_of_injective f hi)
  rw [Nat.card_eq_fintype_card,Fintype.card_perm] at hd
  exact (hp.dvd_factorial.mp hd).trans_eq (Nat.card_eq_fintype_card.symm)

/-- Below twice that prime degree, absence of global fixed points forces transitivity. -/
theorem simple_small_action_pretransitive (G X : Type*) [Group G] [Finite G] [Finite X]
    [MulAction G X] [IsSimpleGroup G] (p : ℕ) (hp : p.Prime) (hpg : p ∣ Nat.card G)
    (hsize : Nat.card X < 2*p) (hmove : ∀ x : X, ∃ g : G, g • x ≠ x) :
    MulAction.IsPretransitive G X := by
  classical
  constructor
  intro x y
  by_cases he : orbit G x = orbit G y
  · have hy : y ∈ orbit G x := he ▸ mem_orbit_self y
    exact hy
  · have hd := (orbit.eq_or_disjoint (G := G) x y).resolve_left he
    let f : orbit G x ⊕ orbit G y → X := Sum.elim Subtype.val Subtype.val
    have hf : Function.Injective f := by
      intro u v h
      cases u with
      | inl u =>
        cases v with
        | inl v => exact congrArg Sum.inl (Subtype.ext h)
        | inr v =>
          change u.val = v.val at h
          exact False.elim (Set.disjoint_left.mp hd u.prop (h.symm ▸ v.prop))
      | inr u =>
        cases v with
        | inl v =>
          change u.val = v.val at h
          exact False.elim (Set.disjoint_left.mp hd v.prop (h ▸ u.prop))
        | inr v => exact congrArg Sum.inr (Subtype.ext h)
    have hc := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at hc
    have hx := simple_orbit_prime_bound G X p hp hpg x (hmove x)
    have hy := simple_orbit_prime_bound G X p hp hpg y (hmove y)
    omega

end Atlas.GroupTheory
