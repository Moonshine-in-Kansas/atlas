import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.SetTheory.Cardinal.NatCard

/-! A finite solvable normal subgroup is detected by normal prime-power subgroups. -/
namespace Atlas.Algebra

variable {G : Type*} [Group G] [Finite G]

 theorem abelian_normal_eq_bot_of_no_normal_pgroup
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Subgroup G) [P.Normal], IsPGroup p P → P = ⊥)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] : A = ⊥ := by
  classical
  by_contra hA
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (ne_of_gt (Finite.one_lt_card (α := A)))
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := Classical.choice inferInstance
  haveI : P.Characteristic := P.characteristic_of_normal inferInstance
  have hb := h p ((P : Subgroup A).map A.subtype) (P.isPGroup'.map A.subtype)
  have he : (P : Subgroup A) = ⊥ := by
    apply (Subgroup.map_injective A.subtype_injective)
    simpa using hb
  exact P.ne_bot_of_dvd_card hd he

 theorem solvable_normal_eq_bot_of_no_normal_pgroup
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Subgroup G) [P.Normal], IsPGroup p P → P = ⊥)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] : N = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := N)
  have descend : ∀ k, derivedSeries N k = ⊥ → N = ⊥ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hh := congrArg (Subgroup.map N.subtype) hk
      simpa [← MonoidHom.range_eq_map] using hh
    | succ k ih =>
      intro hk
      let A := derivedSeries N k
      haveI : IsMulCommutative A := Subgroup.commutator_self_eq_bot_iff.mp hk
      let B := A.map N.subtype
      haveI : B.Normal := inferInstance
      haveI : IsMulCommutative B := by
        let e := A.equivMapOfInjective N.subtype N.subtype_injective
        apply isMulCommutative_iff.mpr
        intro x y
        obtain ⟨a, rfl⟩ := e.surjective x
        obtain ⟨b, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, isMulCommutative_iff.mp inferInstance a b]
      have hb : B = ⊥ := abelian_normal_eq_bot_of_no_normal_pgroup h B
      apply ih
      apply Subgroup.map_injective N.subtype_injective
      simpa [B, A] using hb
  exact descend n hn

end Atlas.Algebra
